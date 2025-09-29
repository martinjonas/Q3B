#include "EqualityPropagator.h"

#include <memory>
#include <sstream>

using namespace z3;

expr EqualityPropagator::Apply(const expr &e)
{
    expr current = e;
    while (current.is_app() && e.decl().decl_kind() == Z3_OP_AND) {
        int argsCount = current.num_args();
        bool wasSimplified = false;

        for (int i = 0; i < argsCount; i++) {
            expr variable(*context);
            expr replacement(*context);
            if (getSubstitutableEquality(current.arg(i), &variable,
                                         &replacement)) {
                Z3_ast args[argsCount - 1];

                for (int j = 0; j < argsCount - 1; j++) {
                    args[j] = j < i ? (Z3_ast)current.arg(j)
                                    : (Z3_ast)current.arg(j + 1);
                }

                expr withoutSubstitutedEquality =
                    to_expr(*context, Z3_mk_and(*context, argsCount - 1, args));

                expr_vector src(*context);
                expr_vector dst(*context);

                src.push_back(variable);
                dst.push_back(replacement);

                appliedSubstitutions.push_back({variable, replacement});

                current = withoutSubstitutedEquality.substitute(src, dst);
                wasSimplified = true;
                break;
            }
        }

        if (!wasSimplified) {
            break;
        }
    }

    return current;
}

void EqualityPropagator::ReconstructModel(Model &model)
{
    for (auto it = appliedSubstitutions.rbegin();
         it != appliedSubstitutions.rend(); it++) {
        const auto &[var, subst] = *it;

        std::stringstream variableString;
        variableString << var;

        model[variableString.str()] =
            vectorFromNumeral(substituteModel(subst, model));
    }
}

bool EqualityPropagator::getSubstitutableEquality(const expr &e, expr *variable,
                                                  expr *replacement)
{
    if (e.is_app()) {
        func_decl dec = e.decl();

        if (dec.decl_kind() == Z3_OP_EQ) {
            expr firstArg = e.arg(0);
            if (firstArg.is_app() && firstArg.num_args() == 0 &&
                firstArg.decl().name() != NULL && firstArg.is_bv() &&
                !firstArg.is_numeral()) {
                std::stringstream variableString;
                variableString << firstArg;
                std::stringstream replacementString;
                replacementString << e.arg(1);

                if (replacementString.str().find(variableString.str()) ==
                    std::string::npos) {
                    *variable = firstArg;
                    *replacement = e.arg(1);
                    return true;
                }
            }

            expr secondArg = e.arg(1);
            if (secondArg.is_app() && secondArg.num_args() == 0 &&
                secondArg.decl().name() != NULL && secondArg.is_bv() &&
                !secondArg.is_numeral()) {
                std::stringstream variableString;
                variableString << secondArg;
                std::stringstream replacementString;
                replacementString << e.arg(0);

                if (replacementString.str().find(variableString.str()) ==
                    std::string::npos) {
                    *variable = secondArg;
                    *replacement = e.arg(0);
                    return true;
                }
            }
        } else if (dec.decl_kind() == Z3_OP_NOT && isVar(e.arg(0))) {
            *variable = e.arg(0);
            *replacement = context->bool_val(false);
            return true;
        }
    }

    if (isVar(e) && e.is_bool()) {
        *variable = e;
        *replacement = context->bool_val(true);
        return true;
    }

    return false;
}

bool EqualityPropagator::isVar(const expr &e) const
{
    if (e.is_var()) {
        return true;
    }

    if (e.is_app()) {
        func_decl f = e.decl();
        unsigned num = e.num_args();

        if (num == 0 && f.name() != NULL && !e.is_numeral()) {
            return true;
        }
    }

    return false;
}
