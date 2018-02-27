#include "UnconstrainedVariableSimplifier.h"
#include <fstream>
#include <cmath>
#include "ExprSimplifier.h"

using namespace std;
using namespace z3;

map<string, int> UnconstrainedVariableSimplifier::countVariableOccurences(expr e, vector<BoundVar> &boundVars, bool isPositive)
{
    std::hash<std::vector<BoundVar>> hasher;

    auto item = subformulaVariableCounts.find({e, isPositive});
    if ((item != subformulaVariableCounts.end() && ((item->second).second) == hasher(boundVars)))
    {
	cacheHits++;
	if (dagCounting)
	{
	    map<string, int> varCounts;
	    return varCounts;
	}
	else
	{
	    return (item->second).first;
	}
    }

    map<string, int> varCounts;
    if (e.is_var())
    {
	Z3_ast ast = (Z3_ast)e;
	int deBruijnIndex = Z3_get_index_value(*context, ast);
	varCounts[std::get<0>(boundVars[boundVars.size() - deBruijnIndex - 1])] = 1;
	subformulaAllConstrained[{e, hasher(boundVars)}] = false;
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

	subformulaAllConstrained[{e, hasher(boundVars)}] = false;
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
		auto result = countVariableOccurences(e.arg(0), boundVars, !isPositive);
		subformulaVariableCounts.insert({{e, isPositive}, {result, hasher(boundVars)}});

		subformulaAllConstrained[{e, hasher(boundVars)}] = subformulaAllConstrained[{e.arg(0), hasher(boundVars)}];
		return result;
	    }
	    else if (decl_kind == Z3_OP_IFF || (decl_kind == Z3_OP_EQ && e.arg(0).is_bool()))
	    {
		auto varCountsLp = countVariableOccurences(e.arg(0), boundVars, isPositive);
		auto varCountsRp = countVariableOccurences(e.arg(1), boundVars, isPositive);

		addCounts(varCountsLp, varCounts);
		addCounts(varCountsRp, varCounts);

		subformulaAllConstrained[{e, hasher(boundVars)}] = allConstrained(varCounts);
		return varCounts;
	    }
	    else if (decl_kind == Z3_OP_IMPLIES)
	    {
		auto varCountsL = countVariableOccurences(e.arg(0), boundVars, !isPositive);
		auto varCountsR = countVariableOccurences(e.arg(1), boundVars, isPositive);

		addCounts(varCountsL, varCounts);
		addCounts(varCountsR, varCounts);

		subformulaAllConstrained[{e, hasher(boundVars)}] = allConstrained(varCounts);
		return varCounts;
	    }

	    for (unsigned i = 0; i < num; i++)
	    {
		auto currentVarCounts = countVariableOccurences(e.arg(i), boundVars, isPositive);

		addCounts(currentVarCounts, varCounts);
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

	subformulaVariableCounts.insert({{e, isPositive}, {varCounts, hasher(boundVars)}});
	subformulaAllConstrained[{e, hasher(boundVars)}] = allConstrained(varCounts);
	return varCounts;
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

	auto result = countVariableOccurences(e.body(), newBoundVars, isPositive);
	subformulaVariableCounts.insert({{e, isPositive}, {result, hasher(boundVars)}});
	subformulaAllConstrained[{e, hasher(boundVars)}] = allConstrained(result);

	return result;
    }

    std::cout << e << std::endl;
    assert(false);
    return varCounts;
}

void UnconstrainedVariableSimplifier::SimplifyIte()
{
    std::vector<BoundVar> boundVars;

    //std::cout << "Counting variables" << std::endl;
    variableCounts = countVariableOccurences(expression, boundVars, true);
    //std::cout << "Done" << std::endl;

    bool anyUnconstrained = false;
    for (auto &var : variableCounts)
    {
	if (var.second == 1)
	{
	    anyUnconstrained = true;
	}
    }

    if (!anyUnconstrained)
    {
       //PrintUnconstrained();
	return;
    }

    unsigned oldHash = 0;

    //expression = expression.simplify();
    //expression = ApplyConstantEqualities(expression);

    int i = 0;

    while (oldHash != expression.hash())
    {
	cacheHits = 0;
	//std::cout << "Simplify once" << std::endl;
	//std::cout << expression << std::endl;
	oldHash = expression.hash();

	SimplifyOnce();

	// std::cout << "--------- Simplify once ------------" << std::endl;
	// std::cout << expression << std::endl;
	// std::cout << "--------- Simplify      ------------" << std::endl;
	expression = expression.simplify();
	// std::cout << expression << std::endl;
	// std::cout << "------------------------------------" << std::endl;
	//expression = simplifier.PushNegations(expression);

	subformulaVariableCounts.clear();
	subformulaAllConstrained.clear();
	std::vector<BoundVar> boundVars;
	//std::cout << "Counting variables" << std::endl;
	variableCounts = countVariableOccurences(expression, boundVars, true);
	//std::cout << "Done" << std::endl;

	trueSimplificationCache.clear();
	falseSimplificationCache.clear();

	i++;
	//PrintUnconstrained();
    }

    //PrintUnconstrained();
}

z3::expr UnconstrainedVariableSimplifier::simplifyOnce(expr e, std::vector<BoundVar> boundVars, bool isPositive = true)
{
    std::hash<std::vector<BoundVar>> hasher;

    if (e.is_var() || e.is_numeral() || subformulaAllConstrained[{e, hasher(boundVars)}])
    {
	return e;
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
	    //std::cout << "cache hit: " << e << " -> " << (item->second).first << std::endl;

	    return (item->second).first;
	}
    }

    if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();
	auto decl_kind = f.decl_kind();

	if (decl_kind == Z3_OP_BADD && num == 2)
	{
	    if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		return e.arg(0);
	    }
	    else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
		return e.arg(1);
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

		Z3_ast returnAst;

		if (mulReplacementMode == SHIFT)
		{
		    returnAst = Z3_mk_bvshl(*context, (Z3_ast)e.arg(0), (Z3_ast)(context->bv_val(zeroes, e.arg(0).get_sort().bv_size())));
		}
		else if (mulReplacementMode == MUL)
		{
		    returnAst = (Z3_ast)(context->bv_val(1 << zeroes, e.arg(0).get_sort().bv_size()) * e.arg(0));
		}
		return to_expr(*context, returnAst);
	    }
	    else if (unconstrained1 && e.arg(0).is_numeral())
	    {
		int zeroes = getNumberOfLeadingZeroes(e.arg(0));

		if (zeroes == 0) return e.arg(1);

		if (mulReplacement == ALL || mulReplacement == LINEAR)
		{
		    Z3_ast returnAst;

		    if (mulReplacementMode == SHIFT)
		    {
			returnAst = Z3_mk_bvshl(*context, (Z3_ast)e.arg(1), (Z3_ast)(context->bv_val(zeroes, e.arg(1).get_sort().bv_size())));
		    }
		    else if (mulReplacementMode == MUL)
		    {
			returnAst = (Z3_ast)(context->bv_val(1 << zeroes, e.arg(1).get_sort().bv_size()) * e.arg(1));
		    }
		    return to_expr(*context, returnAst);
		}
	    }
	    else if (mulReplacement == ALL && unconstrained0 && isBefore(e.arg(1), e.arg(0), boundVars, isPositive))
	    {
		expr arg1 = simplifyOnce(e.arg(1), boundVars, isPositive);

		int bvSize = e.arg(0).get_sort().bv_size();
		expr returnExpr = e.arg(0);

		for (int i = bvSize - 1; i >= 0; i--)
		{
		    Z3_ast shiftAst = Z3_mk_bvshl(*context, (Z3_ast)arg1, (Z3_ast)(context->bv_val(i, e.arg(1).get_sort().bv_size())));
		    returnExpr = ite(arg1.extract(i,i) != 0, to_expr(*context, shiftAst), returnExpr);
		}

		return returnExpr;
	    }
	    else if (mulReplacement == ALL && unconstrained1 && isBefore(e.arg(0), e.arg(1), boundVars, isPositive))
	    {
		expr arg0 = simplifyOnce(e.arg(0), boundVars, isPositive);

		int bvSize = e.arg(1).get_sort().bv_size();
		expr returnExpr = e.arg(1);

		for (int i = bvSize - 1; i >= 0; i--)
		{
		    Z3_ast shiftAst = Z3_mk_bvshl(*context, (Z3_ast)arg0, (Z3_ast)(context->bv_val(i, e.arg(0).get_sort().bv_size())));
		    returnExpr = ite(arg0.extract(i,i) != 0, to_expr(*context, shiftAst), returnExpr);
		}

		return returnExpr;
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
//		    std::cout << "replacing " << e << " by " << (isPositive ? context->bool_val(true) : e.arg(0) == minValue) << std::endl;
		    return isPositive ? context->bool_val(true) : e.arg(0) == minValue;
		}
		else
		{
		    return isPositive ? e.arg(0) == minValue : context->bool_val(true);
		}
	    }
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

	    if (ss.str() != "true" && ss.str() != "false")
	    {
		//std::cout << "result: " << (variableCounts.at(ss.str()) == 1) << std::endl;
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
    auto item = subformulaMaxDeBruijnIndices.find({e, boundVars});
    if (item != subformulaMaxDeBruijnIndices.end())
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

	    subformulaMaxDeBruijnIndices.insert({{e, boundVars}, maxLevel});
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

void UnconstrainedVariableSimplifier::addCounts(std::map<std::string, int> &from, std::map<std::string, int> &to)
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

bool UnconstrainedVariableSimplifier::allConstrained(std::map<std::string, int> &varCounts)
{
    for (auto &var : varCounts)
    {
	if (var.second == 1)
	{
	    return false;
	}
    }

    return true;
}
