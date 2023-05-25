#ifndef TERMCONSTINTRODUCER_H
#define TERMCONSTINTRODUCER_H
#include "z3++.h"
#include <set>
#include <vector>
#include <map>
#include <unordered_map>
#include <iostream>

struct OpVar
{
    z3::expr result;
    Z3_decl_kind op;
    z3::expr l;
    z3::expr r;

OpVar(z3::expr result, Z3_decl_kind op, z3::expr l, z3::expr r) :
    result(result), op(op), l(l), r(r)
    {
    }

    friend bool operator < (OpVar const& lhs, OpVar const& rhs);
    friend bool operator == (OpVar const& lhs, OpVar const& rhs);
};

class TermConstIntroducer
{
public:
    TermConstIntroducer(z3::context &ctx)
    {
      this->context = &ctx;
    }

    z3::expr FlattenMul(const z3::expr&);

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

	bool operator == (const Var& rhs) const
	{
	    return name == rhs.name;
	}
    };

    z3::context* context;
    std::pair<z3::expr, std::set<OpVar>> flattenMulRec(const z3::expr&, const std::vector<Var>&);

    std::map<std::string, std::set<z3::expr>> varsLInMul;
    std::map<std::string, std::set<z3::expr>> varsRInMul;

    void fillVarsInMul(const z3::expr&);

    bool isVar(z3::expr);

    std::set<Z3_ast> fillVarsCache;
    std::map<const Z3_ast, std::tuple<z3::expr, const std::vector<Var>, std::set<OpVar>>> flattenMulCache;
};


#endif // EXPRSIMPLIFIER_H
