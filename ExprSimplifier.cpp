#include "ExprSimplifier.h"

using namespace z3;

expr ExprSimplifier::Simplify(const expr e)
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

