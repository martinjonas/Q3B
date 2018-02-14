#include "ExprSimplifier.h"
#include "UnconstrainedVariableSimplifier.h"
#include <string>
#include <sstream>
#include <vector>
#include <algorithm>

using namespace z3;

#define DEBUG false

expr ExprSimplifier::Simplify(expr expression)
{
    unsigned oldHash = 0;

    if (DEBUG)
    {
	std::cout << std::endl << std::endl << "input:" << std::endl;
	std::cout << expression << std::endl;
    }

    int i = 0;

    if (propagateUnconstrained)
    {
	//expression = CanonizeBoundVariables(expression);
    }

    while (oldHash != expression.hash())
    {
	if (expression.is_const())
	{
	    return expression;
	}

	i++;
	oldHash = expression.hash();

	clearCaches();

	expression = PushQuantifierIrrelevantSubformulas(expression);
	expression = ApplyConstantEqualities(expression);

	for (int i = 0; i < 4; i++)
	{
	    expression = negate(expression);
	    expression = applyDer(expression);
	}

	clearCaches();

	expression = RefinedPushQuantifierIrrelevantSubformulas(expression);
	expression = applyDer(expression);

	for (int i = 0; i < 2; i++)
	{
	    expression = negate(expression);
	    expression = applyDer(expression);
	}

	if (propagateUnconstrained)
	{
	    expression = expression.simplify();

	    UnconstrainedVariableSimplifier unconstrainedSimplifier(*context, expression);
	    unconstrainedSimplifier.SetCountVariablesLocally(true);

	    unconstrainedSimplifier.SimplifyIte();
	    expression = unconstrainedSimplifier.GetExpr();
	}
    }

    if (DEBUG)
    {
        UnconstrainedVariableSimplifier unconstrainedSimplifier(*context, expression);
        unconstrainedSimplifier.PrintUnconstrained();
    }

    pushNegationsCache.clear();
    expression = expression.simplify();
    expression = PushNegations(expression);

    if (DEBUG)
    {
	std::cout << std::endl << std::endl << "nnf:" << std::endl;
	std::cout << expression << std::endl;
    }

    context->check_error();
    clearCaches();

    return expression;
}

expr ExprSimplifier::ApplyConstantEqualities(const expr &e)
{
    if (e.is_app())
    {
        func_decl dec = e.decl();

        if (dec.name().str() == "and")
        {
            int argsCount = e.num_args();

            for (int i=0; i < argsCount; i++)
            {
                expr variable(*context);
                expr replacement(*context);
                if (getSubstitutableEquality(e.arg(i), &variable, &replacement))
                {
                    Z3_ast args [argsCount-1];

                    for (int j=0; j < argsCount-1; j++)
                    {
			args[j] = j < i ? (Z3_ast)e.arg(j) : (Z3_ast)e.arg(j+1);
		    }

                    expr withoutSubstitutedEquality = to_expr(*context, Z3_mk_and(*context, argsCount - 1, args));

                    expr_vector src(*context);
                    expr_vector dst(*context);

                    src.push_back(variable);
                    dst.push_back(replacement);

                    expr substituted = withoutSubstitutedEquality.substitute(src, dst);

                    return ApplyConstantEqualities(substituted);
                }
            }
        }
    }

    return e;
}

expr ExprSimplifier::PushQuantifierIrrelevantSubformulas(const expr &e)
{
    auto item = pushIrrelevantCache.find((Z3_ast)e);
    if (item != pushIrrelevantCache.end())
    {
        return item->second;
    }

    if (!e.get_sort().is_bool())
    {
        return e;
    }

    if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(PushQuantifierIrrelevantSubformulas(e.arg(i)));
        }

        expr result = dec(arguments);
        pushIrrelevantCache.insert({(Z3_ast)e, result});
        return result;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;
        int numBound = Z3_get_quantifier_num_bound(*context, ast);

        if (e.body().is_app())
        {
            func_decl innerDecl = e.body().decl();

            expr_vector bodyVector(*context);
            expr_vector replacementVector(*context);

            if (innerDecl.decl_kind() == Z3_OP_AND || innerDecl.decl_kind() == Z3_OP_OR)
            {
                int numInnerArgs = e.body().num_args();
                for (int i = 0; i < numInnerArgs; i++)
                {
                    expr arg = e.body().arg(i);

                    if (!isRelevant(arg, numBound, 0))
                    {
                        replacementVector.push_back(decreaseDeBruijnIndices(arg, numBound, -1));
                    }
                    else
                    {
                        bodyVector.push_back(arg);
                    }
                }

		expr bodyExpr = innerDecl(bodyVector);
                replacementVector.push_back(modifyQuantifierBody(e, PushQuantifierIrrelevantSubformulas(bodyExpr)));

		expr result = innerDecl(replacementVector);
                pushIrrelevantCache.insert({(Z3_ast)e, result});
                return result;
            }
        }

	expr result = modifyQuantifierBody(e, PushQuantifierIrrelevantSubformulas(e.body()));
        pushIrrelevantCache.insert({(Z3_ast)e, result});

        return result;
    }
    else
    {
        return e;
    }
}

expr ExprSimplifier::RefinedPushQuantifierIrrelevantSubformulas(const expr &e)
{
    auto item = refinedPushIrrelevantCache.find((Z3_ast)e);
    if (item != refinedPushIrrelevantCache.end())
    {
        return item->second;
    }

    if (!e.get_sort().is_bool())
    {
        return e;
    }

    if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(RefinedPushQuantifierIrrelevantSubformulas(e.arg(i)));
        }

        expr result = dec(arguments);
        refinedPushIrrelevantCache.insert({e, result});
        return result;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);

	if (e.body().is_app())
        {
	    Z3_sort sorts [numBound];
	    Z3_symbol decl_names [numBound];
	    for (int i = 0; i < numBound; i++)
	    {
		sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
		decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
	    }

            func_decl innerDecl = e.body().decl();

            expr_vector bodyVector(*context);
            expr_vector replacementVector(*context);

            if (innerDecl.decl_kind() == Z3_OP_AND || innerDecl.decl_kind() == Z3_OP_OR)
            {
                int numInnerArgs = e.body().num_args();

                for (int i = 0; i < numInnerArgs; i++)
                {
                    expr arg = e.body().arg(i);

                    if (!isRelevant(arg, 1, 0))
                    {
                        replacementVector.push_back(decreaseDeBruijnIndices(arg, 1, -1));
                    }
                    else
                    {
                        bodyVector.push_back(arg);
                    }
                }

                Z3_sort outerSorts [numBound-1];
                Z3_symbol outerDecl_names [numBound-1];
                for (int i = 0; i < numBound-1; i++)
                {
                    outerSorts[i] = sorts[i];
                    outerDecl_names[i] = decl_names[i];
                }

                Z3_sort innerSorts [1];
                Z3_symbol innerDecl_names [1];
                innerSorts[0] = sorts[numBound-1];
                innerDecl_names[0] = decl_names[numBound-1];

                expr bodyExpr = innerDecl(bodyVector);
                Z3_ast innerQuantAst = Z3_mk_quantifier(
		    *context,
		    Z3_is_quantifier_forall(*context, ast),
		    Z3_get_quantifier_weight(*context, ast),
		    0,
		    {},
		    1,
		    innerSorts,
		    innerDecl_names,
		    (Z3_ast)RefinedPushQuantifierIrrelevantSubformulas(bodyExpr));

                replacementVector.push_back(to_expr(*context, innerQuantAst));
                expr outerBody = innerDecl(replacementVector);

                if (numBound == 1)
                {
                    expr result = outerBody;
                    refinedPushIrrelevantCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else
                {
                    Z3_ast outerQuantAst = Z3_mk_quantifier(
			*context,
			Z3_is_quantifier_forall(*context, ast),
			Z3_get_quantifier_weight(*context, ast),
			0,
			{},
			numBound-1,
			outerSorts,
			outerDecl_names,
			(Z3_ast)outerBody);

                    expr result = to_expr(*context, outerQuantAst);
                    refinedPushIrrelevantCache.insert({(Z3_ast)e, result});
                    return result;
                }
            }
        }

	expr result = modifyQuantifierBody(e, RefinedPushQuantifierIrrelevantSubformulas(e.body()));
        refinedPushIrrelevantCache.insert({(Z3_ast)e, result});
        return result;
    }
    else
    {
        return e;
    }
}

bool ExprSimplifier::getSubstitutableEquality(const expr &e, expr *variable, expr *replacement)
{
    if (e.is_app())
    {
        func_decl dec = e.decl();

        if (dec.decl_kind() == Z3_OP_EQ)
        {
            expr firstArg = e.arg(0);
            if (firstArg.is_app() && firstArg.num_args() == 0 && firstArg.decl().name() != NULL && firstArg.is_bv() && !firstArg.is_numeral())
            {
		std::stringstream variableString;
		variableString << firstArg;
		std::stringstream replacementString;
		replacementString << e.arg(1);

		if (replacementString.str().find(variableString.str()) == std::string::npos)
		{
		    *variable = firstArg;
		    *replacement = e.arg(1);
		    return true;
		}
            }

	    expr secondArg = e.arg(1);
	    if (secondArg.is_app() && secondArg.num_args() == 0 && secondArg.decl().name() != NULL && secondArg.is_bv() && !secondArg.is_numeral())
            {
		std::stringstream variableString;
		variableString << secondArg;
		std::stringstream replacementString;
		replacementString << e.arg(0);

		if (replacementString.str().find(variableString.str()) == std::string::npos)
		{
		    *variable = secondArg;
		    *replacement = e.arg(0);
		    return true;
		}
            }
        }
	else if (dec.decl_kind() == Z3_OP_NOT && isVar(e.arg(0)))
	{
	    *variable = e.arg(0);
	    *replacement = context->bool_val(false);
	    return true;
	}
    }

    if (isVar(e) && e.is_bool())
    {
    	*variable = e;
    	*replacement = context->bool_val(true);
    	return true;
    }

    return false;
}

expr ExprSimplifier::decreaseDeBruijnIndices(const expr &e, int decreaseBy, int leastIndexToDecrease)
{
    auto item = decreaseDeBruijnCache.find(std::make_tuple((Z3_ast)e, decreaseBy, leastIndexToDecrease));
    if (item != decreaseDeBruijnCache.end())
    {
        return item->second;
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);

        if (deBruijnIndex > leastIndexToDecrease)
        {
            return to_expr(*context, Z3_mk_bound(*context, deBruijnIndex - decreaseBy, (Z3_sort)e.get_sort()));
        }
        else
        {
            return e;
        }
    }
    else if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(decreaseDeBruijnIndices(e.arg(i), decreaseBy, leastIndexToDecrease));
        }

        expr result = dec(arguments);
        decreaseDeBruijnCache.insert({std::make_tuple((Z3_ast)e, decreaseBy, leastIndexToDecrease), result});
        return result;

    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;
        int numBound = Z3_get_quantifier_num_bound(*context, ast);

	expr result = modifyQuantifierBody(e, decreaseDeBruijnIndices(e.body(), decreaseBy, leastIndexToDecrease + numBound));
        decreaseDeBruijnCache.insert({std::make_tuple((Z3_ast)e, decreaseBy, leastIndexToDecrease), result});
        return result;
    }
    else
    {
        return e;
    }
}

expr ExprSimplifier::negate(const expr &e)
{
    assert(e.get_sort().is_bool());

    if (e.is_quantifier())
    {
	return flipQuantifierAndModifyBody(e, negate(e.body()));
    }

    return !e;
}

expr ExprSimplifier::PushNegations(const expr &e)
{
    auto item = pushNegationsCache.find((Z3_ast)e);
    if (false && item != pushNegationsCache.end())
    {
        return item->second;
    }

    if (e.is_app())
    {
        if (e.decl().decl_kind() != Z3_OP_NOT)
        {
            func_decl dec = e.decl();
            int numArgs = e.num_args();

            expr_vector arguments(*context);
            for (int i = 0; i < numArgs; i++)
            {
                if (e.arg(i).is_bool())
                {
                    arguments.push_back(PushNegations(e.arg(i)));
                }
                else
                {
                    arguments.push_back(e.arg(i));
                }
            }

            auto result = dec(arguments);
            pushNegationsCache.insert({(Z3_ast)e, result});
            return result;
        }
        else
        {
            expr notBody = e.arg(0);
            if (notBody.is_app())
            {
                func_decl innerDecl = notBody.decl();
                int numArgs = notBody.num_args();

                if (innerDecl.decl_kind() == Z3_OP_NOT)
                {
                    auto result = PushNegations(notBody.arg(0));
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_AND)
                {
                    expr_vector arguments(*context);
                    for (int i = 0; i < numArgs; i++)
                    {
                        arguments.push_back(PushNegations(!notBody.arg(i)));
                    }

                    auto result = mk_or(arguments);
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_OR)
                {
                    expr_vector arguments(*context);
                    for (int i = 0; i < numArgs; i++)
                    {
                        arguments.push_back(PushNegations(!notBody.arg(i)));
                    }

                    auto result = mk_and(arguments);
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_ITE)
                {
                    auto result = (PushNegations(notBody.arg(0)) && PushNegations(!notBody.arg(1))) || (PushNegations(!notBody.arg(0)) && PushNegations(!notBody.arg(2)));
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
                else if (innerDecl.decl_kind() == Z3_OP_IFF)
                {
                    auto result = (PushNegations(notBody.arg(0)) && PushNegations(!notBody.arg(1))) || (PushNegations(!notBody.arg(0)) && PushNegations(notBody.arg(1)));
                    //pushNegationsCache.insert({(Z3_ast)e, result});
                    return result;
                }
		else if (innerDecl.decl_kind() == Z3_OP_SLEQ)
		{
		    return notBody.arg(1) < notBody.arg(0);
		}
		else if (innerDecl.decl_kind() == Z3_OP_SLT)
		{
		    return notBody.arg(1) <= notBody.arg(0);
		}
		else if (innerDecl.decl_kind() == Z3_OP_ULEQ)
		{
		    return to_expr(*context, Z3_mk_bvult(*context, (Z3_ast)notBody.arg(1), (Z3_ast)notBody.arg(0)));
		}
		else if (innerDecl.decl_kind() == Z3_OP_ULT)
		{
		    return to_expr(*context, Z3_mk_bvule(*context, (Z3_ast)notBody.arg(1), (Z3_ast)notBody.arg(0)));
		}
            }
            else if (notBody.is_quantifier())
            {

                auto result = flipQuantifierAndModifyBody(notBody, PushNegations(!notBody.body()));
                //pushNegationsCache.insert({(Z3_ast)e, result});
                return result;
            }

            auto result = e;
            //pushNegationsCache.insert({(Z3_ast)e, result});
            return result;
        }
    }
    if (e.is_quantifier())
    {
	expr result = modifyQuantifierBody(e, PushNegations(e.body()));
        pushNegationsCache.insert({(Z3_ast)e, result});
        return result;
    }

    auto result = e;
    pushNegationsCache.insert({(Z3_ast)e, result});
    return result;
}

expr ExprSimplifier::CanonizeBoundVariables(const expr &e)
{
    if (e.is_app())
    {
	func_decl dec = e.decl();
	int numArgs = e.num_args();

	expr_vector arguments(*context);
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

	int numBound = Z3_get_quantifier_num_bound(*context, ast);

	Z3_sort sorts [numBound];
	Z3_symbol decl_names [numBound];
	for (int i = 0; i < numBound; i++)
        {
	    sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	    decl_names[i] = Z3_mk_string_symbol(*context, std::to_string(lastBound).c_str());
	    lastBound++;
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
	    (Z3_ast)CanonizeBoundVariables(e.body() && context->bool_val(true)));

	auto result = to_expr(*context, quantAst);
	return result;
    }
    else
    {
	return e;
    }
}

bool ExprSimplifier::isRelevant(const expr &e, int boundVariables, int currentDepth)
{
    auto item = isRelevantCache.find(std::make_tuple((Z3_ast)e, boundVariables, currentDepth));
    if (item != isRelevantCache.end())
    {
        return item->second;
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);

        bool result = (deBruijnIndex - currentDepth) < boundVariables;
        isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), result});
        return result;
    }
    else if (e.is_app())
    {
        int numArgs = e.num_args();

        for (int i = 0; i < numArgs; i++)
        {
            bool relevant = isRelevant(e.arg(i), boundVariables, currentDepth);
            if (relevant)
            {
                isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), true});
                return true;
            }
        }

        isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), false});
        return false;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);

        bool result = isRelevant(e.body(), boundVariables, currentDepth + numBound);
        isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), result});
        return result;
    }
    else
    {
        isRelevantCache.insert({std::make_tuple((Z3_ast)e, boundVariables, currentDepth), false});
        return false;
    }
}

expr ExprSimplifier::mk_or(expr_vector &args)
{
    std::vector<Z3_ast> array;
    for (unsigned i = 0; i < args.size(); i++)
        array.push_back(args[i]);
    return to_expr(args.ctx(), Z3_mk_or(args.ctx(), array.size(), &(array[0])));
}

expr ExprSimplifier::mk_and(expr_vector &args)
{
    std::vector<Z3_ast> array;
    for (unsigned i = 0; i < args.size(); i++)
        array.push_back(args[i]);
    return to_expr(args.ctx(), Z3_mk_and(args.ctx(), array.size(), &(array[0])));
}

expr ExprSimplifier::modifyQuantifierBody(expr quantifierExpr, expr newBody)
{
    Z3_ast ast = (Z3_ast)quantifierExpr;

    int numBound = Z3_get_quantifier_num_bound(*context, ast);

    Z3_sort sorts [numBound];
    Z3_symbol decl_names [numBound];
    for (int i = 0; i < numBound; i++)
    {
	sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
    }

    Z3_ast newAst = Z3_mk_quantifier(
	*context,
	Z3_is_quantifier_forall(*context, ast),
	Z3_get_quantifier_weight(*context, ast),
	0,
	{},
	numBound,
	sorts,
	decl_names,
	(Z3_ast)newBody);

    return to_expr(*context, newAst);
}

expr ExprSimplifier::flipQuantifierAndModifyBody(expr quantifierExpr, expr newBody)
{
    Z3_ast ast = (Z3_ast)quantifierExpr;

    int numBound = Z3_get_quantifier_num_bound(*context, ast);

    Z3_sort sorts [numBound];
    Z3_symbol decl_names [numBound];
    for (int i = 0; i < numBound; i++)
    {
	sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
	decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
    }

    Z3_ast newAst = Z3_mk_quantifier(
	*context,
	!Z3_is_quantifier_forall(*context, ast),
	Z3_get_quantifier_weight(*context, ast),
	0,
	{},
	numBound,
	sorts,
	decl_names,
	(Z3_ast)newBody);

    return to_expr(*context, newAst);
}

z3::expr ExprSimplifier::applyDer(const z3::expr &expression)
{
    z3::goal g(*context);
    g.add(expression);

    z3::tactic derTactic =
	z3::tactic(*context, "simplify") &
	z3::tactic(*context, "elim-and") &
	z3::tactic(*context, "der") &
	z3::tactic(*context, "simplify") &
	z3::tactic(*context, "distribute-forall") &
	z3::tactic(*context, "simplify");

    z3::apply_result result = derTactic(g);

    assert(result.size() == 1);
    z3::goal simplified = result[0];
    return simplified.as_expr();
}

void ExprSimplifier::clearCaches()
{
    pushIrrelevantCache.clear();
    refinedPushIrrelevantCache.clear();
    decreaseDeBruijnCache.clear();
    isRelevantCache.clear();
}

bool ExprSimplifier::isVar(expr e)
{
    if (e.is_var())
    {
        return true;
    }

    if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num == 0 && f.name() != NULL && !e.is_numeral())
	{
	    return true;
	}
    }

    return false;
}

z3::expr ExprSimplifier::FlattenMul(const z3::expr &e)
{
    varsLInMul.clear();
    varsRInMul.clear();
    fillVarsInMul(e);

    auto [newExpr, mulVars] = flattenMulRec(e, {});

    for (const auto &mulVar : mulVars)
    {
	newExpr = mulVar.result == mulVar.l * mulVar.r && newExpr;
    }

    return newExpr;
}

std::pair<z3::expr, std::set
	  <MulVar>> ExprSimplifier::flattenMulRec(const z3::expr &e, const std::vector<Var> &boundVars)
{
    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        return {boundVars[boundVars.size() - deBruijnIndex - 1].expr, {}};
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned numArgs = e.num_args();
	auto decl_kind = f.decl_kind();

	//TODO: also BVMUL of arity > 2
	if (decl_kind == Z3_OP_BMUL && numArgs == 2 && isVar(e.arg(0)) && isVar(e.arg(1)))
	{
	    z3::expr lVar = e.arg(0);
	    z3::expr rVar = e.arg(1);

	    if (lVar.is_var())
	    {
		Z3_ast ast = (Z3_ast)e.arg(0);
		int deBruijnIndex = Z3_get_index_value(*context, ast);
		lVar = boundVars[boundVars.size() - deBruijnIndex - 1].expr;
	    }

	    if (rVar.is_var())
	    {
		Z3_ast ast = (Z3_ast)e.arg(1);
		int deBruijnIndex = Z3_get_index_value(*context, ast);
		rVar = boundVars[boundVars.size() - deBruijnIndex - 1].expr;
	    }

	    std::stringstream newName;
	    newName << "bvmul_" << lVar << "_" << rVar;
	    auto newMulExpr = context->bv_const(newName.str().c_str(), e.get_sort().bv_size());

	    //replace by a new variable and return singleton set of added mulvars
	    return {newMulExpr, {MulVar(newMulExpr, lVar, rVar)}};
	}
	else
	{
	    std::set<MulVar> mulVars;

	    expr_vector arguments(*context);
	    for (uint i = 0U; i < numArgs; i++)
	    {
		auto [newExpr, newMulVars] = flattenMulRec(e.arg(i), boundVars);
		arguments.push_back(newExpr);
		mulVars.insert(newMulVars.begin(), newMulVars.end());
	    }

	    expr result = f(arguments);
	    return {result, mulVars};
	}
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);
	BoundType boundType;
	auto newBoundVars = boundVars;

	boundType = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;

	expr_vector currentBound(*context);
	for (int i = 0; i < numBound; i++)
	{
	    sort s(*context, Z3_get_quantifier_bound_sort(*context, ast, i));
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    auto name = current_symbol.str();
	    if (s.is_bool())
	    {
		Var v(name, boundType, context->bool_const(name.c_str()));
		newBoundVars.push_back(v);
		currentBound.push_back(v.expr);
	    }
	    else if (s.is_bv())
	    {
		Var v(name, boundType, context->bv_const(name.c_str(), s.bv_size()));
		newBoundVars.push_back(v);
		currentBound.push_back(v.expr);
	    }
	    else
	    {
		std::cout << "Unsupported quantifier sort" << std::endl;
		std::cout << "unknown" << std::endl;
		abort();
	    }
	}

	auto [newBody, mulVars] = flattenMulRec(e.body(), newBoundVars);
	std::set<MulVar> quantifiedMulVars;

	for (int i = 0; i < numBound; i++)
	{
	    sort s(*context, Z3_get_quantifier_bound_sort(*context, ast, i));
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    if (s.is_bv())
	    {
		auto v = context->bv_const(current_symbol.str().c_str(), s.bv_size());
		std::copy_if(mulVars.begin(),
			     mulVars.end(),
			     std::inserter(quantifiedMulVars, quantifiedMulVars.end()),
			     [=] (auto mulVar)
			     {
				 return v.to_string() == mulVar.l.to_string() ||
				     v.to_string() == mulVar.r.to_string();

			     });

		//TODO: Do not traverse twice
		std::set<MulVar> newMulVars;
		std::copy_if(mulVars.begin(),
			     mulVars.end(),
			     std::inserter(quantifiedMulVars, quantifiedMulVars.end()),
			     [=] (auto mulVar)
			     {
				 return v.to_string() != mulVar.l.to_string() &&
				     v.to_string() != mulVar.r.to_string();

			     });
		mulVars = newMulVars;
	    }
	}

	for (const auto &mulVar : quantifiedMulVars)
	{
	    newBody =  mulVar.result == mulVar.l * mulVar.r && newBody;

	    for (const auto &v1 : varsLInMul)
	    {
		for (const auto &v2 : varsRInMul)
		{
		    std::stringstream newName;
		    newName << "bvmul_" << v1 << "_" << v2;
		    auto equivMul = context->bv_const(newName.str().c_str(),
						      mulVar.result.get_sort().bv_size());

		    newBody = newBody &&
			implies(v1 == mulVar.l && v2 == mulVar.r,
			    mulVar.result == equivMul);
		}
	    }

	    newBody = newBody.simplify();
	    newBody = exists(mulVar.result,
			     newBody);
	}

	if (boundType == UNIVERSAL)
	{
	    return {forall(currentBound, newBody), mulVars};
	}
	else
	{
	    return {exists(currentBound, newBody), mulVars};
	}
    }

    std::cout << "FlattenMul: unsupported expression" << std::endl;
    std::cout << "unknown" << std::endl;
    abort();
}

bool operator < (MulVar const& lhs, MulVar const& rhs)
{
    return lhs.result.to_string() < rhs.result.to_string();
}

bool operator == (MulVar const& lhs, MulVar const& rhs)
{
    return lhs.result.to_string() == rhs.result.to_string();
}

void ExprSimplifier::fillVarsInMul(const z3::expr &e)
{
    if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned numArgs = e.num_args();
	auto decl_kind = f.decl_kind();

	//TODO: also BVMUL of arity > 2
	if (decl_kind == Z3_OP_BMUL && numArgs == 2 && isVar(e.arg(0)) && isVar(e.arg(1)))
	{
	    if (!e.arg(0).is_var())
	    {
		varsLInMul.insert(e.arg(0));
	    }

	    if (!e.arg(1).is_var())
	    {
		varsRInMul.insert(e.arg(1));
	    }

	}
	else
	{
	    for (uint i = 0U; i < numArgs; i++)
	    {
		fillVarsInMul(e.arg(i));
	    }
	}
    }
    else if (e.is_quantifier())
    {
	fillVarsInMul(e.body());
    }
}
