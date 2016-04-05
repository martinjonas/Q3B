#include "ExprSimplifier.h"
#include "UnconstrainedVariableSimplifier.h"
#include <string>
#include <sstream>
#include <vector>
#include <algorithm>

#include <chrono>
using namespace std::chrono;

using namespace z3;

#define DEBUG false

expr ExprSimplifier::Simplify(expr expression)
{        
    unsigned oldHash = 0;  

    //expression = expression.simplify();
    //expression = ApplyConstantEqualities(expression);    

    //return expression.simplify();

    if (DEBUG)
    {
      std::cout << std::endl << std::endl << "input:" << std::endl;
      std::cout << expression << std::endl;
    }

    int i = 0;
    while (oldHash != expression.hash())
    {
      i++;
      oldHash = expression.hash();

      clearCaches();

      expression = PushQuantifierIrrelevantSubformulas(expression);
      expression = ApplyConstantEqualities(expression);            

      expression = negate(expression);
      expression = applyDer(expression);      

      expression = negate(expression);
      expression = applyDer(expression);                  

      expression = negate(expression);
      expression = applyDer(expression);    

      expression = negate(expression);
      expression = applyDer(expression);

      clearCaches();      

      expression = RefinedPushQuantifierIrrelevantSubformulas(expression);
      expression = applyDer(expression);

      expression = negate(expression);
      expression = applyDer(expression);

      expression = negate(expression);
      expression = applyDer(expression);

      if (propagateUnconstrained)
      {
        UnconstrainedVariableSimplifier unconstrainedSimplifier(*context, expression);        

        pushNegationsCache.clear();
        expression = expression.simplify();
        expression = PushNegations(expression);

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
    //expression = UnflattenAddition(expression);

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
            //std::cout << "simplifying top-level and" << std::endl;
            int argsCount = e.num_args();

            for (int i=0; i < argsCount; i++)
            {
                expr variable(*context);
                expr replacement(*context);
                if (getSubstitutableEquality(e.arg(i), &variable, &replacement))
                {
                    //std::cout << "substitutable equality found: " << e.arg(i) << std::endl;

                    Z3_ast args [argsCount-1];

                    for (int j=0; j < argsCount-1; j++)
                    {
                        if (j < i)
                        {
                            args[j] = (Z3_ast)e.arg(j);
                        }
                        else
                        {
                            args[j] = (Z3_ast)e.arg(j+1);
                        }
                    }                   

                    expr withoutSubstitutedEquality = to_expr(*context, Z3_mk_and(*context, argsCount - 1, args));

                    expr_vector src(*context);
                    expr_vector dst(*context);

                    //std::cout << "withoutSubstituted: " << withoutSubstitutedEquality << std::endl;
                    src.push_back(variable);
                    dst.push_back(replacement);

                    //std::cout << "substituting " << variable << " by " << replacement << std::endl;
                    expr substituted = withoutSubstitutedEquality.substitute(src, dst);
                    //std::cout << "substituted: " << substituted << std::endl;

                    return ApplyConstantEqualities(substituted);
                }
            }

            return e;
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
        //expr_vector bound(*context);
        Z3_sort sorts [numBound];
        Z3_symbol decl_names [numBound];
        for (int i = 0; i < numBound; i++)
        {
            sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
            decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
            //Z3_get_quantifier_bound_name()
            //bound.push_back(e.arg(i));
        }

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
                    bool relevant = isRelevant(arg, numBound, 0);

                    if (!relevant)
                    {
                        replacementVector.push_back(decreaseDeBruijnIndices(arg, numBound, -1));
                    }
                    else
                    {
                        bodyVector.push_back(arg);
                    }
                }

                expr bodyExpr = innerDecl(bodyVector);
                Z3_ast quantAst = Z3_mk_quantifier(
                            *context,
                            Z3_is_quantifier_forall(*context, ast),
                            Z3_get_quantifier_weight(*context, ast),
                            0,
                            {},
                            numBound,
                            sorts,
                            decl_names,
                            (Z3_ast)PushQuantifierIrrelevantSubformulas(bodyExpr));

                replacementVector.push_back(to_expr(*context, quantAst));

                expr result = innerDecl(replacementVector);
                pushIrrelevantCache.insert({(Z3_ast)e, result});
                return result;
            }
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
                    (Z3_ast)PushQuantifierIrrelevantSubformulas(e.body()));

        expr result = to_expr(*context, quantAst);
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
        //expr_vector bound(*context);
        Z3_sort sorts [numBound];
        Z3_symbol decl_names [numBound];
        for (int i = 0; i < numBound; i++)
        {
            sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
            decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
            //Z3_get_quantifier_bound_name()
            //bound.push_back(e.arg(i));
        }

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
                    bool relevant = isRelevant(arg, 1, 0);

                    if (!relevant)
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
                //std::cout << outerBody << std::endl;

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

        Z3_ast quantAst = Z3_mk_quantifier(
                    *context,
                    Z3_is_quantifier_forall(*context, ast),
                    Z3_get_quantifier_weight(*context, ast),
                    0,
                    {},
                    numBound,
                    sorts,
                    decl_names,
                    (Z3_ast)RefinedPushQuantifierIrrelevantSubformulas(e.body()));

        expr result = to_expr(*context, quantAst);
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

        if (dec.name().str() == "=")
        {
            expr firstArg = e.arg(0);
            if (firstArg.is_app() && firstArg.num_args() == 0 && firstArg.decl().name() != NULL && firstArg.is_bv() && !firstArg.is_numeral())
            {
                *variable = firstArg;
                *replacement = e.arg(1);
                return true;
            }
        }
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
                    (Z3_ast)decreaseDeBruijnIndices(e.body(), decreaseBy, leastIndexToDecrease + numBound));

        expr result = to_expr(*context, quantAst);
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
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);

        Z3_sort sorts [numBound];
        Z3_symbol decl_names [numBound];
        for (int i = 0; i < numBound; i++)
        {
            sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
            decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
        }

        Z3_ast quantAst = Z3_mk_quantifier(
                    *context,
                    !Z3_is_quantifier_forall(*context, ast),
                    Z3_get_quantifier_weight(*context, ast),
                    0,
                    {},
                    numBound,
                    sorts,
                    decl_names,
                    (Z3_ast)negate(e.body()));
        return to_expr(*context, quantAst);
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

    if (!e.get_sort().is_bool())
    {
        std::cout << e << std::endl;
    }
    //assert(e.get_sort().is_bool());

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
            }
            else if (notBody.is_quantifier())
            {
                Z3_ast ast = (Z3_ast)notBody;

                int numBound = Z3_get_quantifier_num_bound(*context, ast);

                Z3_sort sorts [numBound];
                Z3_symbol decl_names [numBound];
                for (int i = 0; i < numBound; i++)
                {
                    sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
                    decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
                }

                Z3_ast quantAst = Z3_mk_quantifier(
                            *context,
                            !Z3_is_quantifier_forall(*context, ast),
                            Z3_get_quantifier_weight(*context, ast),
                            0,
                            {},
                            numBound,
                            sorts,
                            decl_names,
                            (Z3_ast)PushNegations(!notBody.body()));
                auto result = to_expr(*context, quantAst);
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
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);

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
                    (Z3_ast)PushNegations(e.body()));
        auto result = to_expr(*context, quantAst);
        pushNegationsCache.insert({(Z3_ast)e, result});
        return result;
    }

    auto result = e;
    pushNegationsCache.insert({(Z3_ast)e, result});
    return result;
}

expr ExprSimplifier::PropagateInequalities(expr e)
{
    if (e.is_app())
    {
        func_decl f = e.decl();
        unsigned num = e.num_args();
        std::string name = f.name().str();

        bool substitute = false;
        expr substituteVar = e;
        expr substituteResult = e;
        expr substitutionReason = e;

        if (name == "or")
        {
            for (unsigned int i = 0; i < num; i++)
            {
                if (e.arg(i).is_app() && e.arg(i).decl().name().str() == "not" && e.arg(i).arg(0).is_app() && e.arg(i).arg(0).decl().name().str() == "=")
                {
                    auto eqExpr = e.arg(i).arg(0);
                    if (isVar(eqExpr.arg(0)))
                    {
                        substitute = true;
                        substituteVar = eqExpr.arg(0);
                        substituteResult = eqExpr.arg(1);
                        substitutionReason = eqExpr;
                    }
                    else if (isVar(eqExpr.arg(1)))
                    {
                        substitute = true;
                        substituteVar = eqExpr.arg(1);
                        substituteResult = eqExpr.arg(0);
                        substitutionReason = eqExpr;
                    }
                }
            }
        }

        if (substitute)
        {
            expr_vector arguments(*context);
            for (unsigned int i = 0; i < num; i++)
            {
                if (e.arg(i) != substitutionReason)
                {
                    arguments.push_back(e.arg(i));
                }
            }

            e = substitutionReason || PropagateInequalities(f(arguments));
        }

        expr_vector arguments(*context);
        for (unsigned int i = 0; i < num; i++)
        {
            arguments.push_back(PropagateInequalities(e.arg(i)));
        }

        auto result = f(arguments);
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
                    (Z3_ast)PropagateInequalities(e.body()));
        auto result = to_expr(*context, quantAst);
        return result;
    }

    return e;
}

expr ExprSimplifier::UnflattenAddition(const expr &e)
{
    auto item = unflattenAdditionCache.find((Z3_ast)e);
    if (item != unflattenAdditionCache.end())
    {
        return item->second;
    }

    if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        if (dec.name().str() == "bvadd")
        {
            if (numArgs == 1)
            {
                return e.arg(0);
            }
            else if (numArgs > 2)
            {
                std::vector<expr> arguments;
                for (int i = 0; i < numArgs; i++)
                {
                    arguments.push_back(e.arg(i));
                }

                std::cout << "in: " << e << std::endl;

                std::sort(arguments.begin(), arguments.end(), [this](const expr& a, const expr& b) -> bool
                {
                    bool seenA = seenAddends.find(a) != seenAddends.end();
                    bool seenB = seenAddends.find(b) != seenAddends.end();

                    if (seenA == seenB)
                    {
                        return (Z3_ast)a > (Z3_ast)b;
                    }
                    else
                    {
                        return seenA < seenB;
                    }
                });

                expr result = arguments.back();
                arguments.pop_back();

                while(arguments.size() != 0)
                {
                    result = dec(arguments.back(), result);
                    seenAddends.insert(arguments.back());
                    arguments.pop_back();
                }

                std::cout << "out: " << result << std::endl;

                return result;
            }
            else
            {
                return e;
            }
        }
        else
        {
            expr_vector arguments(*context);
            for (int i = 0; i < numArgs; i++)
            {
                arguments.push_back(UnflattenAddition(e.arg(i)));
            }

            expr result = dec(arguments);
            unflattenAdditionCache.insert({(Z3_ast)e, result});
            return result;
        }
    }
    else if (e.is_quantifier())
    {
        seenAddends.clear();

        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);
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
                    (Z3_ast)UnflattenAddition(e.body()));

        expr result = to_expr(*context, quantAst);
        unflattenAdditionCache.insert({(Z3_ast)e, result});
        return result;
    }
    else
    {
        unflattenAdditionCache.insert({(Z3_ast)e, e});
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
            z3::tactic(*context, "macro-finder") &
            z3::tactic(*context, "simplify") &
            z3::tactic(*context, "quasi-macros") &
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
    else if (e.is_app())
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
