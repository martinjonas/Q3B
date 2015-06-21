#include "ExprSimplifier.h"
#include <string>
#include <sstream>

using namespace z3;

expr ExprSimplifier::Simplify(const expr &e)
{
    if (e.is_app())
    {
        func_decl dec = e.decl();

        if (dec.name().str() == "and")
        {
            std::cout << "simplifying top-level and" << std::endl;
            int argsCount = e.num_args();

            for (int i=0; i < argsCount; i++)
            {
                expr variable(*context);
                expr replacement(*context);
                if (getSubstitutableEquality(e.arg(i), &variable, &replacement))
                {
                    std::cout << "substitutable equality found: " << e.arg(i) << std::endl;

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

                    expr substituted = withoutSubstitutedEquality.substitute(src, dst);
                    //std::cout << "substituted: " << substituted << std::endl;

                    return Simplify(substituted);
                }
            }

            std::cout << "nothing done" << std::endl;

            return e;
        }
    }

    return e;
}

expr ExprSimplifier::PushQuantifierIrrelevantSubformulas(const expr &e)
{
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

        return dec(arguments);
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
                std::stringstream ss;                
                for (int i = 0; i < numInnerArgs; i++)
                {
                    ss.str("");
                    expr arg = e.body().arg(i);
                    ss << arg << std::flush;
                    std::cout << arg << std::endl;
                    std::string argString = ss.str();

                    bool relevant = false;
                    for (int index = 0; index < numBound; index++)
                    {
                        ss.str("");
                        ss << "(:var " << index << ")";

                        if (argString.find(ss.str()) != std::string::npos)
                        {
                            relevant = true;
                            break;
                        }
                    }

                    if (!relevant)
                    {
                        replacementVector.push_back(decreaseDeBruijnIndices(arg, numBound));
                        std::cout << "not relevant: " << arg << std::endl;                        
                    }
                    else
                    {
                        bodyVector.push_back(arg);
                        std::cout << "relevant: " << arg << std::endl;
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
                return innerDecl(replacementVector);
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
        return to_expr(*context, quantAst);
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

expr ExprSimplifier::decreaseDeBruijnIndices(const expr &e, int decreaseBy)
{
    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);

        return to_expr(*context, Z3_mk_bound(*context, deBruijnIndex - decreaseBy, (Z3_sort)e.get_sort()));
    }
    else if (e.is_app())
    {
        func_decl dec = e.decl();
        int numArgs = e.num_args();

        expr_vector arguments(*context);
        for (int i = 0; i < numArgs; i++)
        {
            arguments.push_back(decreaseDeBruijnIndices(e.arg(i), decreaseBy));
        }

        return dec(arguments);
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
                    (Z3_ast)decreaseDeBruijnIndices(e.body(), decreaseBy));
        return to_expr(*context, quantAst);
    }
    else
    {
        return e;
    }
}
