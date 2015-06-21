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

private:
    z3::context* context;
    bool getSubstitutableEquality(const z3::expr&, z3::expr*, z3::expr*);
    z3::expr decreaseDeBruijnIndices(const z3::expr&, int);
};

#endif // EXPRSIMPLIFIER_H
