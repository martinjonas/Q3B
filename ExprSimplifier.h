#ifndef EXPRSIMPLIFIER_H
#define EXPRSIMPLIFIER_H

#include "z3++.h"

class ExprSimplifier
{
public:
    ExprSimplifier(z3::context &ctx)
    {
      this->context = &ctx;
    }

    z3::expr Simplify(const z3::expr&);
    z3::expr PushQuantifierIrrelevantSubformulas(const z3::expr&);
    z3::expr RefinedPushQuantifierIrrelevantSubformulas(const z3::expr&);
    z3::expr negate(const z3::expr);
    z3::expr PushNegations(const z3::expr&);

private:
    z3::context* context;
    bool getSubstitutableEquality(const z3::expr&, z3::expr*, z3::expr*);
    z3::expr decreaseDeBruijnIndices(const z3::expr&, int, int);
    bool isRelevant(const z3::expr&, int, int);
    z3::expr mk_or(z3::expr_vector&);
    z3::expr mk_and(z3::expr_vector&);

};


#endif // EXPRSIMPLIFIER_H
