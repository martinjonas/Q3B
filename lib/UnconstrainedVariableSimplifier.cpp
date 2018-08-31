#include "UnconstrainedVariableSimplifier.h"
#include <fstream>
#include <cmath>
#include "ExprSimplifier.h"
#include <algorithm>

using namespace std;
using namespace z3;

map<string, int> UnconstrainedVariableSimplifier::countVariableOccurences(expr e, std::list<z3::expr>& boundVars, bool isPositive, Goal goal = NONE)
{
    expr_vector boundVarVector(*context);

    for (const auto& var : boundVars)
    {
        boundVarVector.push_back(var);
    }

    if (e.get_sort().is_bv())
    {
        auto exprWithBoundVars = e.substitute(boundVarVector).simplify();
        auto item = subformulaVariableCounts.find({exprWithBoundVars, isPositive, goal});
        if (item != subformulaVariableCounts.end())
        {
            cacheHits++;
            if (dagCounting)
            {
                map<string, int> varCounts;
                return varCounts;
            }
            else
            {
                return (item->second);
            }
        }
    }

    map<string, int> varCounts;
    if (e.is_var())
    {
	Z3_ast ast = (Z3_ast)e;
	int deBruijnIndex = Z3_get_index_value(*context, ast);
        varCounts[boundVarVector[deBruijnIndex].decl().name().str()] = 1;
	return varCounts;
    }
    else if (e.is_const() && !e.is_numeral())
    {
	if (e.get_sort().is_bool())
	{
	    stringstream ss;
	    ss << e;

	    if (ss.str() == "true" || ss.str() == "false")
	    {
		return varCounts;
	    }

	    varCounts[ss.str()] = 1;
	}
	else if (e.get_sort().is_bv())
	{
	    stringstream ss;
	    ss << e;

	    varCounts[ss.str()] = 1;
	}

	return varCounts;
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num != 0)
	{
	    auto decl_kind = e.decl().decl_kind();

	    if (decl_kind == Z3_OP_NOT)
	    {
		return countVariableOccurences(e.arg(0), boundVars, !isPositive);
	    }
	    else if (decl_kind == Z3_OP_IFF || (decl_kind == Z3_OP_EQ && e.arg(0).is_bool()))
	    {
		addCounts(countVariableOccurences(e.arg(0), boundVars, isPositive), varCounts);
		addCounts(countVariableOccurences(e.arg(1), boundVars, isPositive), varCounts);

		return varCounts;
	    }
	    else if (decl_kind == Z3_OP_IMPLIES)
	    {
		addCounts(countVariableOccurences(e.arg(0), boundVars, !isPositive), varCounts);
		addCounts(countVariableOccurences(e.arg(1), boundVars, isPositive), varCounts);

		return varCounts;
	    }
	    else if (decl_kind == Z3_OP_ITE)
	    {
		auto varCountsElse = countVariableOccurences(e.arg(2), boundVars, isPositive);

		//counts(ite(a, b, c)) = counts(a) + max(counts(b), counts(c))
		addCounts(countVariableOccurences(e.arg(0), boundVars, isPositive), varCounts);
		maxCounts(countVariableOccurences(e.arg(1), boundVars, isPositive), varCountsElse);
		addCounts(std::move(varCountsElse), varCounts);

		return varCounts;
	    }

            if (decl_kind == Z3_OP_ULEQ || decl_kind == Z3_OP_ULT)
            {
                addCounts(countVariableOccurences(e.arg(0), boundVars, isPositive, UNSIGN_MIN), varCounts);
                addCounts(countVariableOccurences(e.arg(1), boundVars, isPositive, UNSIGN_MAX), varCounts);
                return varCounts;
            }

            if (decl_kind == Z3_OP_UGEQ || decl_kind == Z3_OP_UGT)
            {
                addCounts(countVariableOccurences(e.arg(0), boundVars, isPositive, UNSIGN_MAX), varCounts);
                addCounts(countVariableOccurences(e.arg(1), boundVars, isPositive, UNSIGN_MIN), varCounts);
                return varCounts;
            }

            if (decl_kind == Z3_OP_SLEQ || decl_kind == Z3_OP_SLT)
            {
                addCounts(countVariableOccurences(e.arg(0), boundVars, isPositive, SIGN_MIN), varCounts);
                addCounts(countVariableOccurences(e.arg(1), boundVars, isPositive, SIGN_MAX), varCounts);
                return varCounts;
            }

            if (decl_kind == Z3_OP_SGEQ || decl_kind == Z3_OP_SGT)
            {
                addCounts(countVariableOccurences(e.arg(0), boundVars, isPositive, SIGN_MAX), varCounts);
                addCounts(countVariableOccurences(e.arg(1), boundVars, isPositive, SIGN_MIN), varCounts);
                return varCounts;
            }

            for (unsigned i = 0; i < num; i++)
            {
                addCounts(countVariableOccurences(e.arg(i), boundVars, isPositive), varCounts);
            }
	}
	else if (f.name() != NULL)
	{
	    z3::sort s = f.range();

	    if ((s.is_bv() && !e.is_numeral()) || (s.is_bool() && !e.is_const()))
	    {
		stringstream ss;
		ss << e;
		varCounts[ss.str()] = 1;
	    }
	}

        if (e.get_sort().is_bv())
        {
            auto exprWithBoundVars = e.substitute(boundVarVector).simplify();
            subformulaVariableCounts.insert({{exprWithBoundVars, isPositive, goal}, varCounts});
            subformulaVariableCounts.insert({{exprWithBoundVars, !isPositive, goal}, varCounts});
        }
	return varCounts;
    }
    else if(e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;
	int numBound = Z3_get_quantifier_num_bound(*context, ast);

        std::list<z3::expr> newBoundVars = boundVars;

	for (int i = 0; i < numBound; i++)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
            Z3_sort z3_sort = Z3_get_quantifier_bound_sort(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);
            z3::sort current_sort(*context, z3_sort);

            if (current_sort.is_bool())
            {
                newBoundVars.push_front(context->bool_const(current_symbol.str().c_str()));
            }
            else //is BV
            {
                newBoundVars.push_front(context->bv_const(current_symbol.str().c_str(), current_sort.bv_size()));
            }
	}

	auto result = countVariableOccurences(e.body(), newBoundVars, isPositive);

	return result;
    }

    std::cout << e << std::endl;
    assert(false);
    return varCounts;
}

void UnconstrainedVariableSimplifier::SimplifyIte()
{
    std::vector<BoundVar> boundVars;
    variableCounts = countFormulaVarOccurences(expression);

    bool anyUnconstrained = std::any_of(variableCounts.begin(), variableCounts.end(), [](const auto& var) { return var.second == 1; });
    if (!anyUnconstrained)
    {
	return;
    }

    unsigned oldHash = 0;

    while (oldHash != expression.hash())
    {
	oldHash = expression.hash();

	SimplifyOnce();
	expression = expression.simplify();

	subformulaVariableCounts.clear();
	std::vector<BoundVar> boundVars;
	variableCounts = countFormulaVarOccurences(expression);

	trueSimplificationCache.clear();
	falseSimplificationCache.clear();
    }
}

z3::expr UnconstrainedVariableSimplifier::simplifyOnce(expr e, std::vector<BoundVar> boundVars, bool isPositive = true, Goal goal = NONE)
{
    if (e.is_var() || e.is_numeral())
    {
	return e;
    }

    if (forcedGoal.has_value())
    {
        goal = forcedGoal.value();
    }

    cacheMapType::iterator item;

    if (isPositive)
    {
	item = trueSimplificationCache.find(e);
    }
    else
    {
	item = falseSimplificationCache.find(e);
    }

    if (((isPositive && item != trueSimplificationCache.end()) || (!isPositive && item != falseSimplificationCache.end())))
    {
	auto cachedBoundVars =  (item->second).second;
	bool correctBoundVars = true;

	int pairsCount = min(boundVars.size(), cachedBoundVars.size());

	for (int i = 0; i < pairsCount; i++)
	{
	    string oldVarName = std::get<0>(cachedBoundVars[cachedBoundVars.size() - i - 1]);
	    string newVarName = std::get<0>(boundVars[boundVars.size() - i - 1]);

	    if (oldVarName != newVarName)
	    {
		correctBoundVars = false;
	    }
	}

	if (correctBoundVars)
	{
	    return (item->second).first;
	}
    }

    if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();
	auto decl_kind = f.decl_kind();

        if (decl_kind == Z3_OP_BADD)
	{
            for (unsigned int i = 0; i < num; i++)
            {
                if (!isUnconstrained(e.arg(i), boundVars))
                {
                    continue;
                }

                bool allBefore = true;
                for (unsigned int j = 0; j < num; j++)
                {
                    if (i != j && !isBefore(e.arg(j), e.arg(i), boundVars, isPositive))
                    {
                        allBefore = false;
                        break;
                    }
                }

                if (allBefore)
                {
                    return e.arg(i);
                }
            }
	}
	else if (decl_kind == Z3_OP_BNOT)
	{
	    if (isUnconstrained(e.arg(0), boundVars))
	    {
		return e.arg(0);
	    }
	}
	else if (decl_kind == Z3_OP_BAND || decl_kind == Z3_OP_BOR || decl_kind == Z3_OP_BXOR)
	{
	    if (isUnconstrained(e.arg(0), boundVars) && isUnconstrained(e.arg(1), boundVars))
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
		    return e.arg(1);
		}
		else
		{
		    return e.arg(0);
		}
	    }
	}
	else if (decl_kind == Z3_OP_BMUL && num == 2)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

	    if (unconstrained0 && unconstrained1)
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
		    return e.arg(1);
		}
		else
		{
		    return e.arg(0);
		}
	    }
	    else if (unconstrained0 && e.arg(1).is_numeral())
	    {
		int zeroes = getNumberOfLeadingZeroes(e.arg(1));

		if (zeroes == 0) return e.arg(0);

		Z3_ast returnAst = nullptr;

		if (mulReplacementMode == SHIFT)
		{
		    returnAst = Z3_mk_bvshl(*context, (Z3_ast)e.arg(0), (Z3_ast)(context->bv_val(zeroes, e.arg(0).get_sort().bv_size())));
		}
		else if (mulReplacementMode == MUL)
		{
		    returnAst = (Z3_ast)(context->bv_val(1 << zeroes, e.arg(0).get_sort().bv_size()) * e.arg(0));
		}
		else if (mulReplacementMode == MASK)
		{
		    returnAst = (-1 << zeroes) & e.arg(0);
		}
		return to_expr(*context, returnAst);
	    }
	    else if (unconstrained1 && e.arg(0).is_numeral())
	    {
		int zeroes = getNumberOfLeadingZeroes(e.arg(0));

		if (zeroes == 0) return e.arg(1);

		if (mulReplacement == ALL || mulReplacement == LINEAR)
		{
		    Z3_ast returnAst = nullptr;

		    if (mulReplacementMode == SHIFT)
		    {
			returnAst = Z3_mk_bvshl(*context, (Z3_ast)e.arg(1), (Z3_ast)(context->bv_val(zeroes, e.arg(1).get_sort().bv_size())));
		    }
		    else if (mulReplacementMode == MUL)
		    {
			returnAst = (Z3_ast)(context->bv_val(1 << zeroes, e.arg(1).get_sort().bv_size()) * e.arg(1));
		    }
		    else if (mulReplacementMode == MASK)
		    {
			returnAst = (-1 << zeroes) & e.arg(1);
		    }
		    return to_expr(*context, returnAst);
		}
	    }
	    else if (mulReplacement == ALL && unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		expr arg1 = e.arg(1);

		int bvSize = e.arg(0).get_sort().bv_size();
		expr ones = context->bv_val(-1, bvSize);
		expr returnExpr = context->bv_val(0, bvSize);

		for (int i = bvSize - 1; i >= 0; i--)
		{
		    if (mulReplacementMode == MASK)
		    {
			auto shiftExpr = e.arg(0) & to_expr(*context,
							    Z3_mk_bvshl(*context, (Z3_ast)ones, (Z3_ast)(context->bv_val(i, e.arg(1).get_sort().bv_size()))));
			returnExpr = ite(arg1.extract(i,i) != 0, shiftExpr, returnExpr);
		    }
		    else
		    {
			Z3_ast shiftAst = Z3_mk_bvshl(*context, (Z3_ast)e.arg(0), (Z3_ast)(context->bv_val(i, e.arg(1).get_sort().bv_size())));
			returnExpr = ite(arg1.extract(i,i) != 0, to_expr(*context, shiftAst), returnExpr);
		    }
		}

		return returnExpr;
	    }
	    else if (mulReplacement == ALL && unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
		expr arg0 = e.arg(0);

		int bvSize = e.arg(1).get_sort().bv_size();
		expr ones = context->bv_val(-1, bvSize);
		expr returnExpr = context->bv_val(0, bvSize);

		for (int i = bvSize - 1; i >= 0; i--)
		{
		    if (mulReplacementMode == MASK)
		    {
			auto shiftExpr = e.arg(1) & to_expr(*context,
							    Z3_mk_bvshl(*context, (Z3_ast)ones, (Z3_ast)(context->bv_val(i, e.arg(1).get_sort().bv_size()))));
			returnExpr = ite(arg0.extract(i,i) != 0, shiftExpr, returnExpr);
		    }
		    else
		    {
			Z3_ast shiftAst = Z3_mk_bvshl(*context, (Z3_ast)e.arg(1), (Z3_ast)(context->bv_val(i, e.arg(0).get_sort().bv_size())));
			returnExpr = ite(arg0.extract(i,i) != 0, to_expr(*context, shiftAst), returnExpr);
		    }
		}

		return returnExpr;
	    }
	}
	else if (decl_kind == Z3_OP_BSHL)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

	    if (unconstrained0 && unconstrained1)
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
		    return e.arg(1);
		}
		else
		{
		    return e.arg(0);
		}
	    }
	    else if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
                expr arg1 = e.arg(1);
		int bvSize = e.arg(1).get_sort().bv_size();
		expr ones = context->bv_val(-1, bvSize);
                expr zeroes = context->bv_val(0, bvSize);
		auto shiftExpr = to_expr(*context, Z3_mk_bvshl(*context, (Z3_ast)ones, (Z3_ast)arg1));

		return (e.arg(0) & shiftExpr);
	    }
	    else if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
                if (isPositive && goalUnconstrained && getBoundType(e.arg(1), boundVars) == EXISTENTIAL)
                {
                    int bvSize = e.arg(1).get_sort().bv_size();
                    expr zeroes = context->bv_val(0, bvSize);
                    if (goal == UNSIGN_MIN)
                    {
                        return zeroes;
                    }
                    else if (goal == SIGN_MIN)
                    {
                        auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
                        return z3::ite(e.arg(0) == 0, zeroes, minSigned);
                    }
                }
	    }
	}
	else if (decl_kind == Z3_OP_BLSHR)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

	    if (unconstrained0 && unconstrained1)
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
		    return e.arg(1);
		}
		else
		{
		    return e.arg(0);
		}
	    }
	    else if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
                int bvSize = e.arg(1).get_sort().bv_size();
		expr arg1 = e.arg(1);
		expr ones = context->bv_val(-1, bvSize);
                expr zeroes = context->bv_val(0, bvSize);

                if (isPositive && goalUnconstrained && getBoundType(e.arg(0), boundVars) == EXISTENTIAL)
                {
                    if (goal == SIGN_MAX)
                    {
                        auto maxSigned = concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1));
                        return z3::ite(arg1 == 0, maxSigned, to_expr(*context, Z3_mk_bvlshr(*context, ones, arg1)));
                    }
                    else if (goal == UNSIGN_MAX)
                    {
                        return to_expr(*context, Z3_mk_bvlshr(*context, ones, arg1));
                    }
                    else if (goal == SIGN_MIN)
                    {
                        auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
                        return z3::ite(arg1 == 0, minSigned, zeroes);
                    }
                    else if (goal == UNSIGN_MIN)
                    {
                        return zeroes;
                    }
                }

		auto shiftExpr = to_expr(*context, Z3_mk_bvlshr(*context, (Z3_ast)ones, (Z3_ast)arg1));
                return (e.arg(0) & shiftExpr);
	    }
            else if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
                int bvSize = e.arg(0).get_sort().bv_size();
		expr arg0 = e.arg(0);
		expr ones = context->bv_val(-1, bvSize);
                expr zeroes = context->bv_val(0, bvSize);

                if (isPositive && goalUnconstrained && getBoundType(e.arg(1), boundVars) == EXISTENTIAL)
                {
                    if (goal == SIGN_MAX)
                    {
                        return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, arg0, f(arg0, 1));
                    }
                    else if (goal == UNSIGN_MAX)
                    {
                        return arg0;
                    }
                    else if (goal == SIGN_MIN)
                    {
                        return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, zeroes, arg0);
                    }
                    else if (goal == UNSIGN_MIN)
                    {
                        return zeroes;
                    }
                }
	    }
	}
	else if (decl_kind == Z3_OP_BASHR)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

	    if (unconstrained0 && unconstrained1)
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
		    return e.arg(1);
		}
		else
		{
		    return e.arg(0);
		}
	    }
	    else if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
                int bvSize = e.arg(1).get_sort().bv_size();
		expr arg1 = e.arg(1);
		expr ones = context->bv_val(-1, bvSize);
                expr zeroes = context->bv_val(0, bvSize);
                auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0

                if (isPositive && goalUnconstrained && getBoundType(e.arg(0), boundVars) == EXISTENTIAL)
                {
                    if (goal == SIGN_MAX)
                    {
                        auto maxSigned = concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1));
                        return to_expr(*context, Z3_mk_bvashr(*context, maxSigned, arg1));
                    }
                    else if (goal == UNSIGN_MAX)
                    {
                        return to_expr(*context, Z3_mk_bvashr(*context, ones, arg1));
                    }
                    else if (goal == SIGN_MIN)
                    {
                        return f(minSigned, arg1);
                    }
                    else if (goal == UNSIGN_MIN)
                    {
                        return context->bv_val(0, bvSize);
                    }
                }

                // can return precisely numbers with the same t+1 most-significant bits

                // (bvashr u t) -> (ite (or (= (bvand u (bvashr minSigned t)) 0)
                //                          (= (bvand u (bvashr minSigned t)) (bvashr minSigned t)))
                //                      u
                //                      0)
                auto onlyTopFromU = e.arg(0) & f(minSigned, e.arg(1));
                return z3::ite(onlyTopFromU == 0 || onlyTopFromU == f(minSigned, e.arg(1)),
                                      e.arg(0),
                                      zeroes);
	    }
	    else if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
                int bvSize = e.arg(0).get_sort().bv_size();
		expr arg0 = e.arg(0);
		expr ones = context->bv_val(-1, bvSize);
                expr zeroes = context->bv_val(0, bvSize);

                if (isPositive && goalUnconstrained && getBoundType(e.arg(1), boundVars) == EXISTENTIAL)
                {
                    if (goal == SIGN_MAX)
                    {
                        return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, arg0, ones);
                    }
                    else if (goal == UNSIGN_MAX)
                    {
                        return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, arg0, ones);
                    }
                    else if (goal == SIGN_MIN)
                    {
                        return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, zeroes, arg0);
                    }
                    else if (goal == UNSIGN_MIN)
                    {
                        return z3::ite(arg0.extract(bvSize-1, bvSize-1) == 0, zeroes, arg0);
                    }
                }
	    }
	}
	else if (decl_kind == Z3_OP_BUREM_I)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

	    if (unconstrained0 && unconstrained1)
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
		    return e.arg(1);
		}
		else
		{
		    return e.arg(0);
		}
	    }
	    else if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		int bvSize = e.arg(1).get_sort().bv_size();
		expr zero = context->bv_val(0, bvSize);
		auto bvult = to_expr(*context, Z3_mk_bvult(*context, (Z3_ast)e.arg(0), (Z3_ast)e.arg(1)));

		// bvurem u t may return all values from {0,...,t-1}
		// (bvurem u t) -> (ite (= t 0) u (ite (bvult u t) u 0))
		return ite(e.arg(1) == zero,
			   e.arg(0),
			   ite(bvult, e.arg(0), zero));
	    }
            else if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
		int bvSize = e.arg(1).get_sort().bv_size();
		expr zero = context->bv_val(0, bvSize);

                if (isPositive && goalUnconstrained && getBoundType(e.arg(1), boundVars) == EXISTENTIAL)
                {
                    if (goal == UNSIGN_MIN)
                    {
                        return zero; //by setting divisor to max
                    }
                    else if (goal == UNSIGN_MAX)
                    {
                        return e.arg(0); //by setting divisor to zero
                    }
                    else if (goal == SIGN_MIN)
                    {
                        //unsigned division can not change positive sign to negative sign
                        //if positive, reduce to zero
                        //if negative, leave the same, because remainder will not decrease the negative number
                        return z3::ite(e.arg(0).extract(bvSize-1, bvSize-1) == 0, zero, e.arg(0));
                    }
                }

                // bvurem t u may return all values from {0,...,(t-1)/2} \cup {t}
		// (bvurem t u) -> (ite (= t 0) 0 ((ite (bvule u (bvudiv (- t 1) 2)) u t)))
                auto bvule = to_expr(*context, Z3_mk_bvule(*context, e.arg(1),
                                                           Z3_mk_bvudiv(*context,
                                                                        (e.arg(0) - context->bv_val(1, bvSize)),
                                                                        context->bv_val(2, bvSize))));
                auto result = z3::ite(e.arg(0) == 0, zero,
                                      z3::ite(bvule, e.arg(1), e.arg(0)));
                return result;
	    }
	}
	else if (decl_kind == Z3_OP_BUDIV_I)
	{
	    bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
	    bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);

	    if (unconstrained0 && unconstrained1)
	    {
		if (isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
		{
		    return e.arg(1);
		}
		else
		{
		    return e.arg(0);
		}
	    }

            if (unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive) &&
                goalUnconstrained && getBoundType(e.arg(1), boundVars) == EXISTENTIAL)
            {
                int bvSize = e.arg(0).get_sort().bv_size();
		expr arg0 = e.arg(0);
		expr ones = context->bv_val(-1, bvSize);
                expr zeroes = context->bv_val(0, bvSize);

                if (goal == UNSIGN_MAX)
                {
                    return ones;
                }
                else if (goal == UNSIGN_MIN)
                {
                    return z3::ite(arg0 == ones, context->bv_val(1, bvSize), zeroes);
                }
                else if (goal == SIGN_MAX)
                {
                    //if positive, do not change, as unsigned division can not increase the number
                    //if negative, divide by 2 to get a positive number
                    return z3::ite(e.arg(0).extract(bvSize-1, bvSize-1) == 0, e.arg(0), f(arg0, 2));
                }
                else if (goal == SIGN_MIN)
                {
                    //if positive, reduce to -1
                    //if negative, do not change, as division would make it positive
                    return z3::ite(e.arg(0).extract(bvSize-1, bvSize-1) == 0, ones, arg0);
                }
            }

	    if (unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		int bvSize = e.arg(1).get_sort().bv_size();
		expr ones = context->bv_val(-1, bvSize);
		expr zero = context->bv_val(0, bvSize);

		auto bvudiv = to_expr(*context, Z3_mk_bvudiv(*context, (Z3_ast)ones, e.arg(1)));
		auto bvule = to_expr(*context, Z3_mk_bvule(*context, (Z3_ast)e.arg(0), bvudiv));

                if (isPositive && goalUnconstrained && getBoundType(e.arg(0), boundVars) == EXISTENTIAL)
                {
                    if (goal == UNSIGN_MIN)
                    {
                        return z3::ite(e.arg(1) == zero, ones, zero);
                    }
                    else if (goal == UNSIGN_MAX)
                    {
                        return z3::ite(e.arg(1) == zero, ones, bvudiv); // for a/0, the max is 11..1, for a/b it is 11...1/b
                    }
                    else if (goal == SIGN_MIN)
                    {
                        auto minSigned = z3::concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)); //1000...0
                        return z3::ite(e.arg(1) == zero,
                                       ones,
                                       z3::ite(e.arg(1) == context->bv_val(1, bvSize),
                                               minSigned,
                                               zero));
                    }
                    else if (goal == SIGN_MAX)
                    {
                        auto maxSigned = concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1));
                        return z3::ite(e.arg(1) == zero,
                                       ones,
                                       z3::ite(e.arg(1) == context->bv_val(1, bvSize),
                                               maxSigned,
                                               bvudiv));
                    }
                }

		// bvurem may return all values from {0,...,(2^32-1)/t}
		// (bvurem u t) -> (ite (= t 0) (11...1) (ite (bvule u (bvudiv (11...1)/t)) u 0))
		return ite(e.arg(1) == zero,
		 	   ones,
		 	   ite(bvule, e.arg(0), zero));
	    }
	}
	else if (decl_kind == Z3_OP_OR)
	{
	    auto toReturn = context->bool_val(false);

	    std::vector<expr> toReturnVec;
	    bool changed = false;

	    for (unsigned int i = 0; i < num; i++)
	    {
		if (isUnconstrained(e.arg(i), boundVars))
		{
		    auto boundType = getBoundType(e.arg(i), boundVars);
		    if ((boundType == EXISTENTIAL && isPositive) || (boundType == UNIVERSAL || isPositive))
		    {
			return context->bool_val(true);
		    }

		    changed = true;
		}
		else
		{
		    toReturnVec.push_back(e.arg(i));
		}
	    }

	    if (changed)
	    {
		for (auto const &toReturnPart : toReturnVec)
		{
		    toReturn = toReturn || toReturnPart;
		}

		return toReturn;
	    }
	}
	else if (decl_kind == Z3_OP_AND)
	{
	    auto toReturn = context->bool_val(true);

	    std::vector<expr> toReturnVec;
	    bool changed = false;

	    for (unsigned int i = 0; i < num; i++)
	    {
		if (isUnconstrained(e.arg(i), boundVars))
		{
		    auto boundType = getBoundType(e.arg(i), boundVars);
		    if ((boundType == EXISTENTIAL && !isPositive) || (boundType == UNIVERSAL && isPositive))
		    {
			return context->bool_val(false);
		    }

		    changed = true;
		}
		else
		{
		    toReturnVec.push_back(e.arg(i));
		}
	    }

	    if (changed)
	    {
		for (auto const &toReturnPart : toReturnVec)
		{
		    toReturn = toReturn && toReturnPart;
		}

		return toReturn;
	    }
	}
	else if (decl_kind == Z3_OP_IFF)
	{
	    return e;
//			return ((simplifyOnce(e.arg(0), boundVars, isPositive) || !simplifyOnce(e.arg(1), boundVars, !isPositive)) &&
//					(!simplifyOnce(e.arg(0), boundVars, !isPositive) || simplifyOnce(e.arg(1), boundVars, isPositive)));
	}
	else if (decl_kind == Z3_OP_NOT)
	{
	    if (isUnconstrained(e.arg(0), boundVars))
	    {
		return e.arg(0);
	    }
	}
	else if (decl_kind == Z3_OP_EQ)
	{
	    if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		auto boundType = getBoundType(e.arg(0), boundVars);
		if (boundType == EXISTENTIAL)
		{
		    return isPositive ? context->bool_val(true) : context->bool_val(false);
		}
		else
		{
		    return isPositive ? context->bool_val(false) : context->bool_val(true);
		}
	    }
	    else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
		auto boundType = getBoundType(e.arg(1), boundVars);

		if (boundType == EXISTENTIAL)
		{
		    return isPositive ? context->bool_val(true) : context->bool_val(false);
		}
		else
		{
		    return isPositive ? context->bool_val(false) : context->bool_val(true);
		}
	    }
	    else
	    {
		if (e.arg(0).is_bool())
		{
		    return e; //or split into implications
		}
		else
		{
		    return simplifyOnce(e.arg(0), boundVars, isPositive) == simplifyOnce(e.arg(1), boundVars, isPositive);
		}
	    }
	}
	else if (decl_kind == Z3_OP_SLEQ || decl_kind == Z3_OP_ULEQ )
	{
	    if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		auto boundType = getBoundType(e.arg(0), boundVars);
		auto bvSize = e.arg(1).get_sort().bv_size();

		auto maxValue = decl_kind == Z3_OP_SLEQ ?
		    concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1)) :
		    context->bv_val(-1, bvSize);

		if (boundType == EXISTENTIAL)
		{
		    return isPositive ? context->bool_val(true) : e.arg(1) == maxValue;
		}
		else
		{
		    return isPositive ? e.arg(1) == maxValue : context->bool_val(true);
		}
	    }
	    else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
		auto boundType = getBoundType(e.arg(1), boundVars);
		auto bvSize = e.arg(1).get_sort().bv_size();

		auto minValue = decl_kind == Z3_OP_SLEQ ?
		    concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)) :
		    context->bv_val(0, bvSize);

		if (boundType == EXISTENTIAL)
		{
		    return isPositive ? context->bool_val(true) : e.arg(0) == minValue;
		}
		else
		{
		    return isPositive ? e.arg(0) == minValue : context->bool_val(true);
		}
	    }

            auto arg0 = simplifyOnce(e.arg(0), boundVars, isPositive, decl_kind == Z3_OP_SLEQ ? SIGN_MIN : UNSIGN_MIN);
            auto arg1 = simplifyOnce(e.arg(1), boundVars, isPositive, decl_kind == Z3_OP_SLEQ ? SIGN_MAX : UNSIGN_MAX);

            return f(arg0, arg1);
	}
	else if (decl_kind == Z3_OP_SLT || decl_kind == Z3_OP_ULT)
	{
	    if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		auto boundType = getBoundType(e.arg(0), boundVars);
		auto bvSize = e.arg(1).get_sort().bv_size();

		auto minValue = decl_kind == Z3_OP_SLT ?
		    concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)) :
		    context->bv_val(0, bvSize);

		if (boundType == EXISTENTIAL)
		{
		    return isPositive ? !(e.arg(1) == minValue) : context->bool_val(false);
		}
		else
		{
		    return isPositive ? context->bool_val(false) : !(e.arg(1) == minValue);
		}
	    }
	    else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
		auto boundType = getBoundType(e.arg(1), boundVars);
		auto bvSize = e.arg(1).get_sort().bv_size();

		auto maxValue = decl_kind == Z3_OP_SLT ?
		    concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1)) :
		    context->bv_val(-1, bvSize);

		if (boundType == EXISTENTIAL)
		{
		    return isPositive ? !(e.arg(0) == maxValue) : context->bool_val(false);
		}
		else
		{
		    return isPositive ? context->bool_val(false) : !(e.arg(0) == maxValue);
		}
	    }

            auto arg0 = simplifyOnce(e.arg(0), boundVars, isPositive, decl_kind == Z3_OP_SLT ? SIGN_MIN : UNSIGN_MIN);
            auto arg1 = simplifyOnce(e.arg(1), boundVars, isPositive, decl_kind == Z3_OP_SLT ? SIGN_MAX : UNSIGN_MAX);

            return f(arg0, arg1);
	}
	else if (decl_kind == Z3_OP_ITE)
	{
            if (isUnconstrained(e.arg(0), boundVars) && isUnconstrained(e.arg(1), boundVars) && getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(1), boundVars))
            {
                return e.arg(1);
            }

            if (isUnconstrained(e.arg(0), boundVars) && isUnconstrained(e.arg(2), boundVars) && getBoundType(e.arg(0), boundVars) == getBoundType(e.arg(2), boundVars))
            {
                return e.arg(2);
            }

	    auto result = ite(e.arg(0), simplifyOnce(e.arg(1), boundVars, isPositive), simplifyOnce(e.arg(2), boundVars, isPositive));
	    if (isPositive)
	    {
		trueSimplificationCache.insert({e, {result, boundVars}});
	    }
	    else
	    {
		falseSimplificationCache.insert({e, {result, boundVars}});
	    }
	    return result;
	}

	expr_vector arguments(*context);
	for (unsigned int i = 0; i < num; i++)
	{
	    if (decl_kind == Z3_OP_NOT)
	    {
		arguments.push_back(simplifyOnce(e.arg(i), boundVars, !isPositive));
	    }
	    else
	    {
		arguments.push_back(simplifyOnce(e.arg(i), boundVars, isPositive));
	    }
	}

	auto result = f(arguments);
	if (isPositive)
	{
	    trueSimplificationCache.insert({e, {result, boundVars}});
	}
	else
	{
	    falseSimplificationCache.insert({e, {result, boundVars}});
	}

	return result;
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);
	BoundType boundType;

	if (isPositive)
	{
	    boundType = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;
	}
	else
	{
	    boundType = Z3_is_quantifier_forall(*context, ast) ? EXISTENTIAL : UNIVERSAL;
	}

	for (int i = 0; i < numBound; i++)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);

	    symbol current_symbol(*context, z3_symbol);

	    int level;
	    if (boundVars.size() == 0)
	    {
		level = 1;
	    }
	    else
	    {
		auto previousVar = boundVars.back();
		level = std::get<2>(previousVar);

		if (boundType != std::get<1>(previousVar))
		{
		    level++;
		}
	    }


	    boundVars.push_back(make_tuple(current_symbol.str(), boundType, level));
	}

	Z3_sort sorts [numBound];
	Z3_symbol decl_names [numBound];
	for (int i = 0; i < numBound; i++)
	{
	    sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	    decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
	}

	Z3_ast quantAst = Z3_mk_quantifier(
	    *context,
	    Z3_is_quantifier_forall(*context, ast),
	    Z3_get_quantifier_weight(*context, ast),
	    0,
	    {},
	    numBound,
	    sorts,
	    decl_names,
	    (Z3_ast)simplifyOnce(e.body(), boundVars, isPositive));
	auto result = to_expr(*context, quantAst);
	return result;
    }

    if (isPositive)
    {
	trueSimplificationCache.insert({e, {e, boundVars}});
    }
    else
    {
	falseSimplificationCache.insert({e, {e, boundVars}});
    }
    return e;
}

bool UnconstrainedVariableSimplifier::isUnconstrained(expr e, const vector<BoundVar> &boundVars) const
{
    if (!isVar(e) && e.is_app())
    {
	return e.decl().decl_kind() == Z3_OP_EXTRACT && isUnconstrained(e.arg(0), boundVars);
    }

    if (e.is_var())
    {
	Z3_ast ast = (Z3_ast)e;
	int deBruijnIndex = Z3_get_index_value(*context, ast);
	return (variableCounts.at(std::get<0>(boundVars.at(boundVars.size() - deBruijnIndex - 1))) == 1);
    }
    else if (e.is_app() && !e.is_numeral())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num == 0 && f.name() != NULL)
	{
	    stringstream ss;
	    ss << e;

            if (forcedConstrained.find(ss.str()) != forcedConstrained.end())
            {
                return false;
            }


	    if (ss.str() != "true" && ss.str() != "false")
	    {
		return (variableCounts.at(ss.str()) == 1);
	    }
	}
    }

    return false;
}

bool UnconstrainedVariableSimplifier::isVar(expr e) const
{
    if (e.is_var())
    {
	return true;
    }
    else if (e.is_app() || e.is_numeral())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num == 0 && f.name() != NULL)
	{
	    return true;
	}
    }

    return false;
}

int UnconstrainedVariableSimplifier::getMaxLevel(expr e, const std::vector<BoundVar> &boundVars, bool isPositive = true)
{
    auto item = subformulaMaxLevels.find({e, boundVars});
    if (item != subformulaMaxLevels.end())
    {
	return item->second;
    }

    if (e.is_var())
    {
	Z3_ast ast = (Z3_ast)e;
	int deBruijnIndex = Z3_get_index_value(*context, ast);
	return std::get<2>(boundVars[boundVars.size() - deBruijnIndex - 1]);
    }
    else if (e.is_const() && !e.is_numeral())
    {
	return -1;
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	int maxLevel = -1;

	if (num != 0)
	{
	    for (unsigned i = 0; i < num; i++)
	    {
		auto currentMaxLevel = getMaxLevel(e.arg(i), boundVars, isPositive);

		if (currentMaxLevel > maxLevel)
		{
		    maxLevel = currentMaxLevel;
		}
	    }

	    subformulaMaxLevels.insert({{e, boundVars}, maxLevel});
	    return maxLevel;
	}
	else if (f.name() != NULL)
	{
	    return -1;
	}
    }
    else if(e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;
	int numBound = Z3_get_quantifier_num_bound(*context, ast);
	BoundType boundType;

	if (isPositive)
	{
	    boundType = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;
	}
	else
	{
	    boundType = Z3_is_quantifier_forall(*context, ast) ? EXISTENTIAL : UNIVERSAL;
	}

	int level;
	if (boundVars.size() == 0)
	{
	    level = 1;
	}
	else
	{
	    auto previousVar = boundVars.back();
	    level = std::get<2>(previousVar);

	    if (boundType != std::get<1>(previousVar))
	    {
		level++;
	    }
	}

	vector<BoundVar> newBoundVars = boundVars;

	for (int i = 0; i < numBound; i++)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    newBoundVars.push_back(make_tuple(current_symbol.str(), boundType, level));
	}

	return getMaxLevel(e.body(), newBoundVars, isPositive);
    }

    assert(false);
    return -1;
}

//should be true if all variables in "a" are quantified before a variable "b"
bool UnconstrainedVariableSimplifier::isBefore(expr a, expr b, const std::vector<BoundVar> &boundVars, bool isPositive)
{
    int aLevel = getMaxLevel(a, boundVars, isPositive);
    int bLevel = getMaxLevel(b, boundVars, isPositive);

    return (aLevel <= bLevel);
}

BoundType UnconstrainedVariableSimplifier::getBoundType(expr e, const std::vector<BoundVar> &boundVars)
{
    if (e.is_var())
    {
	Z3_ast ast = (Z3_ast)e;
	int deBruijnIndex = Z3_get_index_value(*context, ast);
	return std::get<1>(boundVars[boundVars.size() - deBruijnIndex - 1]);
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (f.decl_kind() == Z3_OP_EXTRACT)
	{
	    return getBoundType(e.arg(0), boundVars);
	}

	if (num == 0 && f.name() != NULL)
	{
	    return EXISTENTIAL;
	}
    }

    std::cout << e << std::endl;
    assert(false);
    return EXISTENTIAL;
}

int UnconstrainedVariableSimplifier::getNumberOfLeadingZeroes(const z3::expr &e)
{
    assert(e.is_numeral());

    std::stringstream ss;
    ss << e;

    string numeralString = ss.str();

    int bitSize = e.get_sort().bv_size();

    const string prefix = numeralString.substr(0, 2);
    string valueString = numeralString.substr(2);

    assert(prefix == "#x" || prefix == "#b");

    std::size_t found = valueString.find_last_not_of("0");

    if (prefix == "#b")
    {
	if (found == std::string::npos)
	{
	    return bitSize;
	}
	else
	{
	    return bitSize - found - 1;
	}
    }
    else
    {
	if (found == std::string::npos)
	{
	    return bitSize;
	}
	else
	{
	    int zeroes = bitSize - (found + 1)*4;

	    switch (valueString[found])
	    {
	    case '2':
	    case '6':
	    case 'a':
	    case 'e':
		return zeroes + 1;
	    case '4':
	    case 'c':
		return zeroes + 2;
	    case '8':
		return zeroes + 3;
	    default:
		return zeroes;
	    }
	}

    }
}

expr UnconstrainedVariableSimplifier::CanonizeBoundVariables(const expr &e)
{
    if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(e.ctx());
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(CanonizeBoundVariables(e.arg(i)));
        }

        expr result = dec(arguments);
        return result;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(e.ctx(), ast);

        Z3_sort sorts [numBound];
        Z3_symbol decl_names [numBound];
        for (int i = 0; i < numBound; i++)
        {
            sorts[i] = Z3_get_quantifier_bound_sort(e.ctx(), ast, i);
            decl_names[i] = Z3_mk_string_symbol(e.ctx(), std::to_string(lastBound).c_str());
			lastBound++;
        }

        Z3_ast quantAst = Z3_mk_quantifier(
			e.ctx(),
			Z3_is_quantifier_forall(e.ctx(), ast),
			Z3_get_quantifier_weight(e.ctx(), ast),
			0,
			{},
			numBound,
			sorts,
			decl_names,
			(Z3_ast)CanonizeBoundVariables(e.body() && e.ctx().bool_val(true)));

        auto result = to_expr(e.ctx(), quantAst);
        return result;
    }
    else
    {
        return e;
    }
}

void UnconstrainedVariableSimplifier::addCounts(std::map<std::string, int>&& from, std::map<std::string, int> &to)
{
    for (auto &item : from)
    {
	auto singleVarCount = to.find(item.first);
	if (singleVarCount == to.end())
	{
	    to[item.first] = item.second;
	}
	else
	{
	    if (to[item.first] == 2)
	    {
		continue;
	    }

	    if (singleVarCount->second + item.second > 1)
	    {
		to[item.first] = 2;
	    }
	    else
	    {
		to[item.first] = singleVarCount->second + item.second;
	    }
	}
    }
}

void UnconstrainedVariableSimplifier::maxCounts(std::map<std::string, int>&& from, std::map<std::string, int> &to)
{
    for (auto &item : from)
    {
	auto singleVarCount = to.find(item.first);
	if (singleVarCount == to.end())
	{
	    to[item.first] = item.second;
	}
	else
	{
	    to[item.first] = std::max(singleVarCount->second, item.second);
	}
    }
}


std::map<std::string, int> UnconstrainedVariableSimplifier::countFormulaVarOccurences(z3::expr e)
{
    std::list<z3::expr> boundVars;
    if (e.is_app() && e.decl().decl_kind() == Z3_OP_OR)
    {
	assert(e.num_args() > 0);
	auto variableCounts = countVariableOccurences(e.arg(0), boundVars, true);
	for(unsigned int i = 1; i < e.num_args(); i++)
	{
	    maxCounts(countVariableOccurences(e.arg(i), boundVars, true), variableCounts);
	}
	return variableCounts;
    }

    return countVariableOccurences(e, boundVars, true);
}
