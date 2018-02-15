#ifndef EXPRSIMPLIFIER_H
#define EXPRSIMPLIFIER_H
#include "z3++.h"
#include <map>
#include <vector>

class ExprSimplifier
{
public:
    ExprSimplifier(z3::context &ctx) : propagateUnconstrained(false)
    {
      this->context = &ctx;
    }

    ExprSimplifier(z3::context &ctx, bool propagateUnconstrained) : propagateUnconstrained(propagateUnconstrained)
    {
      this->context = &ctx;
    }

    z3::expr Simplify (z3::expr);
    z3::expr ApplyConstantEqualities(const z3::expr&);
    z3::expr PushQuantifierIrrelevantSubformulas(const z3::expr&);
    z3::expr RefinedPushQuantifierIrrelevantSubformulas(const z3::expr&);
    z3::expr negate(const z3::expr&);
    z3::expr PushNegations(const z3::expr&);
    z3::expr CanonizeBoundVariables(const z3::expr&);

private:
    enum BoundType { EXISTENTIAL, UNIVERSAL };

    struct Var
    {
	std::string name;
	BoundType boundType;
	z3::expr expr;

    Var(std::string name, BoundType boundType, z3::expr e) :
	name(name), boundType(boundType), expr(e)
	    {  }
    };

    std::map<const Z3_ast, z3::expr> refinedPushIrrelevantCache;
    std::map<const Z3_ast, z3::expr> pushIrrelevantCache;
    std::map<std::tuple<const Z3_ast, int, int>, z3::expr> decreaseDeBruijnCache;
    std::map<std::tuple<const Z3_ast, int, int>, bool> isRelevantCache;
    std::map<const Z3_ast, z3::expr> pushNegationsCache;
    void clearCaches();

    z3::context* context;
    bool getSubstitutableEquality(const z3::expr&, z3::expr*, z3::expr*);
    z3::expr decreaseDeBruijnIndices(const z3::expr&, int, int);
    bool isRelevant(const z3::expr&, int, int);
    z3::expr mk_or(z3::expr_vector&);
    z3::expr mk_and(z3::expr_vector&);
    z3::expr modifyQuantifierBody(z3::expr quantifierExpr, z3::expr newBody);
    z3::expr flipQuantifierAndModifyBody(z3::expr quantifierExpr, z3::expr newBody);
    z3::expr applyDer(const z3::expr&);

    bool isVar(z3::expr);
    bool propagateUnconstrained;

    int lastBound = 0;
};


#endif // EXPRSIMPLIFIER_H
