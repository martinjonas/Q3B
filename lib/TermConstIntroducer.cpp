#include "TermConstIntroducer.h"
#include <string>
#include <sstream>
#include <algorithm>

using namespace z3;

bool TermConstIntroducer::isVar(expr e)
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

z3::expr TermConstIntroducer::FlattenMul(const z3::expr &e)
{
    varsLInMul.clear();
    varsRInMul.clear();
    fillVarsInMul(e);

    auto [newExpr, mulVars] = flattenMulRec(e, {});

    for (const auto &mulVar : mulVars)
    {
	newExpr = mulVar.result == mulVar.l * mulVar.r && newExpr;
    }

    varsLInMul.clear();
    varsRInMul.clear();

    return newExpr;
}

std::pair<z3::expr, std::set
	  <MulVar>> TermConstIntroducer::flattenMulRec(const z3::expr &e, const std::vector<Var> &boundVars)
{
    auto item = flattenMulCache.find(e);
    if (item != flattenMulCache.end() && boundVars == std::get<1>(item->second))
    {
	return {std::get<0>(item->second), std::get<2>(item->second)};
    }

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

	    //if bound variable, replace by a corresponding Z3 expr
	    if (lVar.is_var())
	    {
		Z3_ast ast = (Z3_ast)e.arg(0);
		int deBruijnIndex = Z3_get_index_value(*context, ast);
		lVar = boundVars[boundVars.size() - deBruijnIndex - 1].expr;
	    }

	    //if bound variable, replace by a corresponding Z3 expr
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
	    flattenMulCache.insert({(Z3_ast)e, {result, boundVars, mulVars}});
	    return {result, mulVars};
	}
    }
    else if (e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int numBound = Z3_get_quantifier_num_bound(*context, ast);
	BoundType boundType = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;
	auto newBoundVars = boundVars;

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
	    newBody = mulVar.result == mulVar.l * mulVar.r && newBody;

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

	    newBody = exists(mulVar.result, newBody.simplify());
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

void TermConstIntroducer::fillVarsInMul(const z3::expr &e)
{
    auto item = fillVarsCache.find((Z3_ast)e);
    if (item != fillVarsCache.end())
    {
	return;
    }

    fillVarsCache.insert((Z3_ast)e);

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
