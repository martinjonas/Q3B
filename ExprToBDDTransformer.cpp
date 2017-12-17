#include "ExprToBDDTransformer.h"
#include <cmath>
#include <iostream>
#include <sstream>
#include <list>
#include <algorithm>

#include "HexHelper.h"

#define DEBUG false

Bvec ExprToBDDTransformer::bvneg(Bvec bv, int bitSize)
{
    return Bvec::bvec_map1(bv, [&](const BDD &a) { return !a; }) + Bvec::bvec_con(bddManager, bitSize, 1);
}

using namespace std;
using namespace z3;

ExprToBDDTransformer::ExprToBDDTransformer(z3::context &ctx, z3::expr e, InitialOrder initialOrder) : expression(e), initialOrder(initialOrder)
{
    this->context = &ctx;
    bddManager = Cudd();

    loadVars();
    setApproximationType(SIGN_EXTEND);
}

void ExprToBDDTransformer::getVars(const z3::expr &e)
{
    auto item = processedVarsCache.find((Z3_ast)e);
    if (item != processedVarsCache.end())
    {
	return;
    }

    if (e.is_const() && !e.is_numeral())
    {
	stringstream ss;
	ss << e;

	if (ss.str() == "true" || ss.str() == "false")
	{
	    return;
	}

	int bitWidth = e.get_sort().is_bool() ? 1 : e.get_sort().bv_size();
	constSet.insert(make_pair(ss.str(), bitWidth));
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (num == 0 && f.name() != NULL)
	{
            z3::sort s = f.range();

            if (s.is_bv() && !e.is_numeral())
            {
		var c = make_pair(f.name().str(), s.bv_size());
		constSet.insert(c);
            }
            else if (s.is_bool())
            {
                stringstream ss;
                ss << e;
                var c = make_pair(ss.str(), 1);
                constSet.insert(c);
            }
	}
	else
	{
            for (unsigned i = 0; i < num; i++)
            {
		getVars(e.arg(i));
            }
	}
    }
    else if(e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

        for (int i = 0; i < boundVariables; i++)
        {
            Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
            Z3_sort z3_sort = Z3_get_quantifier_bound_sort(*context, ast, i);

            symbol current_symbol(*context, z3_symbol);
            z3::sort current_sort(*context, z3_sort);

	    var c = make_pair(current_symbol.str(), current_sort.is_bool() ? 1 : current_sort.bv_size());
	    boundVarSet.insert(c);
        }

        getVars(e.body());
    }

    processedVarsCache.insert((Z3_ast)e);
}

void ExprToBDDTransformer::loadVars()
{
    getVars(expression);
    processedVarsCache.clear();

    if (DEBUG)
    {
	std::cout << "Bound vars: " << boundVarSet.size() << std::endl;
    }

    set<var> allVars;
    allVars.insert(constSet.begin(), constSet.end());
    allVars.insert(boundVarSet.begin(), boundVarSet.end());

    if (allVars.size() == 0)
    {
        return;
    }

    VariableOrderer orderer(allVars, *context);

    if (initialOrder == HEURISTIC)
    {
        orderer.OrderFor(expression);
    }
    else if (initialOrder == INTERLEAVE_ALL)
    {
        orderer.MergeAll();
    }

    vector<list<var>> orderedGroups = orderer.GetOrdered();

    int maxBitSize = 0;
    for(auto const &v : allVars)
    {
        if (v.second > maxBitSize) maxBitSize = v.second;
    }

    if (DEBUG)
    {
        cout << "Groups: " << orderedGroups.size() << endl;
    }

    int offset = 0;
    for(auto const &group : orderedGroups)
    {
	if (DEBUG)
	{
	    cout << "Group size: " << group.size() << endl;
	}
	int i = 0;
	for (auto const &v : group)
	{
	    int bitnum = v.second;
	    Bvec varBvec = Bvec::bvec_var(bddManager, bitnum, offset + i, group.size());
	    vars.insert({v.first, varBvec});

	    int currentVar = offset + i;

	    varIndices[v.first] = vector<int>();

	    BDD varSet = bddManager.bddOne();
	    for (int bit = 0; bit < bitnum; bit++)
	    {
		varIndices[v.first].push_back(currentVar);
		varSet = varSet * varBvec[bit];
		currentVar += group.size();
	    }

	    varSets.insert({v.first, varSet});

	    i++;
	}

	offset += maxBitSize * group.size();
    }
}

BDD ExprToBDDTransformer::loadBDDsFromExpr(expr e)
{
    bddExprCache.clear();
    bvecExprCache.clear();

    cacheHits = 0;

    this->expression = e;
    BDD result = getBDDFromExpr(e, {}, true);

    bddExprCache.clear();
    bvecExprCache.clear();

    return result;
}

BDD ExprToBDDTransformer::getConjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars)
{
    vector<BDD> results;

    for (unsigned int i = 0; i < arguments.size(); i++)
    {
        BDD argBdd = getBDDFromExpr(arguments[i], boundVars);

        if (argBdd.IsZero())
        {
            return bddManager.bddZero();
        }
        else
        {
            results.push_back(argBdd);
        }
    }

    if (results.size() == 0)
    {
	return bddManager.bddOne();
    }
    else
    {
	std::sort(results.begin(), results.end(),
		  [&](const BDD& a, const BDD& b) -> bool
		  {
		      return bddManager.nodeCount(std::vector<BDD>{a}) < bddManager.nodeCount(std::vector<BDD>{b});
		  });

	BDD toReturn = results.at(0);

	for (unsigned int i = 1; i < results.size(); i++)
	{
	    if (toReturn.IsZero())
	    {
		return bddManager.bddZero();
	    }

	    toReturn = toReturn * results.at(i);
	}

	return toReturn;
    }
}

BDD ExprToBDDTransformer::getDisjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars)
{
    vector<BDD> results;

    for (unsigned int i = 0; i < arguments.size(); i++)
    {
        BDD argBdd = getBDDFromExpr(arguments[i], boundVars);

	if (argBdd.IsOne())
        {
            return bddManager.bddOne();
        }
	else
	{
	    results.push_back(argBdd);
	}
    }

    if (results.size() == 0)
    {
	return bddManager.bddZero();
    }
    else
    {
	std::sort(results.begin(), results.end(),
		  [&](const BDD& a, const BDD& b) -> bool
		  {
		      return bddManager.nodeCount(std::vector<BDD>{a}) < bddManager.nodeCount(std::vector<BDD>{b});
		  });

	BDD toReturn = results.at(0);

	for (unsigned int i = 1; i < results.size(); i++)
	{
	    if (toReturn.IsOne())
	    {
		return bddManager.bddOne();
	    }

	    toReturn = toReturn + results.at(i);
	}

	return toReturn;
    }
}

bool ExprToBDDTransformer::correctBoundVars(const std::vector<boundVar> &boundVars, const std::vector<boundVar> &cachedBoundVars)
{
    int pairsCount = min(boundVars.size(), cachedBoundVars.size());

    for (int i = 0; i < pairsCount; i++)
    {
	string oldVarName = cachedBoundVars[cachedBoundVars.size() - i - 1].first;
	string newVarName = boundVars[boundVars.size() - i - 1].first;

	if (oldVarName != newVarName)
	{
	    return false;
	}
    }

    return true;
}

BDD ExprToBDDTransformer::getBDDFromExpr(const expr &e, vector<boundVar> boundVars, bool onlyExistentials)
{
    assert(e.is_bool());
    //cout << "BDD: " << e << endl;

    auto item = bddExprCache.find((Z3_ast)e);
    if (item != bddExprCache.end())
    {
        if (correctBoundVars(boundVars, (item->second).second))
        {
            return (item->second).first;
        }
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];
        return (vars.at(bVar.first) == Bvec::bvec_true(bddManager, 1));
    }
    else if (e.is_const())
    {
	stringstream ss;
	ss << e;

	if (ss.str() == "true")
	{
	    return bddManager.bddOne();
	}
	else if (ss.str() == "false")
	{
	    return bddManager.bddZero();
	}

	BDD toReturn = (vars.at(ss.str()) == Bvec::bvec_true(bddManager, 1));
	return toReturn;
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	string functionName = f.name().str();
	if (functionName == "=")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "= -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto sort = e.arg(0).get_sort();
	    BDD result;

	    assert(sort.is_bv() || sort.is_bool());
	    if (sort.is_bv())
	    {
		result = getBvecFromExpr(e.arg(0), boundVars) == getBvecFromExpr(e.arg(1), boundVars);
	    }
	    else if (sort.is_bool())
	    {
		result = getBDDFromExpr(e.arg(0), boundVars).Xnor(getBDDFromExpr(e.arg(1), boundVars));
	    }

	    return result;
	}
	else if (functionName == "not")
	{
	    auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
	    return !arg0;
	}
	else if (functionName == "and")
	{
	    vector<expr> arguments;
	    for (unsigned int i = 0; i < num; i++)
	    {
		arguments.push_back(e.arg(i));
	    }

	    BDD result = getConjunctionBdd(arguments, boundVars);
	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "or")
	{
	    vector<expr> arguments;
	    for (unsigned int i = 0; i < num; i++)
	    {
		arguments.push_back(e.arg(i));
	    }

	    BDD result = getDisjunctionBdd(arguments, boundVars);
	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "=>")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "=> -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBDDFromExpr(e.arg(1), boundVars);
	    BDD result = arg0.Xnor(arg1);

	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvule")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvule -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result = getBvecFromExpr(e.arg(0), boundVars) <= getBvecFromExpr(e.arg(1), boundVars);

	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvult")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvult -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result = getBvecFromExpr(e.arg(0), boundVars) < getBvecFromExpr(e.arg(1), boundVars);

	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvuge")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvugr -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result = getBvecFromExpr(e.arg(0), boundVars) >= getBvecFromExpr(e.arg(1), boundVars);

	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvugt")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvugt -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result = getBvecFromExpr(e.arg(0), boundVars) > getBvecFromExpr(e.arg(1), boundVars);

	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvsle")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvsle -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

	    int size = e.arg(0).get_sort().bv_size();

	    BDD head0 = arg0[size-1];
	    BDD head1 = arg1[size-1];

	    Bvec tail0 = arg0.bvec_coerce(size - 1);
	    Bvec tail1 = arg1.bvec_coerce(size - 1);

	    BDD differentSigns = (head0.Xnor(bddManager.bddOne())) * (head1.Xnor(bddManager.bddZero()));

	    BDD sameSigns = head0.Xnor(head1);
	    BDD sameSignsLte = sameSigns * (tail0 <= tail1);

	    BDD result = differentSigns + sameSignsLte;
	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvslt")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvslt -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

	    int size = e.arg(0).get_sort().bv_size();

	    BDD head0 = arg0[size-1];
	    BDD head1 = arg1[size-1];

	    Bvec tail0 = arg0.bvec_coerce(size - 1);
	    Bvec tail1 = arg1.bvec_coerce(size - 1);

	    BDD differentSigns = (head0.Xnor(bddManager.bddOne())) * (head1.Xnor(bddManager.bddZero()));

	    BDD sameSigns = head0.Xnor(head1);
	    BDD sameSignsLth = sameSigns * (tail0 < tail1);

	    BDD result = differentSigns + sameSignsLth;
	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "iff")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "iff -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result = getBDDFromExpr(e.arg(0), boundVars).Xnor(getBDDFromExpr(e.arg(1), boundVars));

	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "if")
	{
	    if (e.num_args() != 3)
	    {
		std::cout << "if -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBDDFromExpr(e.arg(1), boundVars);
	    auto arg2 = getBDDFromExpr(e.arg(2), boundVars);
	    BDD result = arg0.Ite(arg1, arg2);

	    bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else
	{
	    cout << "function " << f.name().str() << endl;
	}
    }
    else if(e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

	for (int i = 0; i < boundVariables; i++)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    BoundType bt = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;
	    boundVars.push_back(std::pair<string, BoundType>(current_symbol.str(), bt));
	}

	BDD bodyBdd;
	if (onlyExistentials)
	{
	    if (Z3_is_quantifier_forall(*context, ast))
	    {
		//only existentials so far, but this one is universal
		bodyBdd = getBDDFromExpr(e.body(), boundVars, false);
	    }
	    else
	    {
		//only existentials so far and this one is also existential
		return getBDDFromExpr(e.body(), boundVars, true);
	    }
	}
	else
	{
	    bodyBdd = getBDDFromExpr(e.body(), boundVars, false);
	}

	for (int i = boundVariables - 1; i >= 0; i--)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    if (Z3_is_quantifier_forall(*context, ast))
	    {
		bodyBdd = bodyBdd.UnivAbstract(varSets.at(current_symbol.str()));
	    }
	    else
	    {
		bodyBdd = bodyBdd.ExistAbstract(varSets[current_symbol.str()]);
	    }
	}

	bddExprCache.insert({(Z3_ast)e, {bodyBdd, boundVars}});
	return bodyBdd;
    }

    cout << "bdd else: " << e << endl;
    abort();
}

Bvec ExprToBDDTransformer::getApproximatedVariable(const std::string& varName, int newBitWidth, const ApproximationType& at)
{
    if (newBitWidth > 0)
    {
	Bvec var = vars.at(varName);

	for (unsigned int i = newBitWidth; i < var.bitnum(); i++)
	{
	    if (at == ZERO_EXTEND)
	    {
		var.set(i, bddManager.bddZero());
	    }
	    else if (at == SIGN_EXTEND)
	    {
		var.set(i, var[i - 1]);
	    }
	}

	return var;
    }
    else
    {
	Bvec var = vars.at(varName);

	for (int i = var.bitnum() - newBitWidth - 1; i >= 0; i--)
	{
	    if (at == ZERO_EXTEND)
	    {
		var.set(i, bddManager.bddZero());
	    }
	    else if (at == SIGN_EXTEND)
	    {
		var.set(i, var[i + 1]);
	    }
	}

	return var;
    }
}

Bvec ExprToBDDTransformer::getBvecFromExpr(const expr &e, vector<boundVar> boundVars)
{
    assert(e.is_bv());
    //cout << e << endl;

    auto item = bvecExprCache.find((Z3_ast)e);
    if (item != bvecExprCache.end())
    {
	if (correctBoundVars(boundVars, (item->second).second))
        {
	    cacheHits++;
            return (item->second).first;
        }
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];

        if (bVar.second == EXISTENTIAL && exisentialBitWidth != 0)
        {
            int bitSize = e.get_sort().bv_size();
	    return getApproximatedVariable(bVar.first, min(exisentialBitWidth, bitSize), approximationType);
        }
        if (bVar.second == UNIVERSAL && universalBitWidth != 0)
        {
	    int bitSize = e.get_sort().bv_size();
	    return getApproximatedVariable(bVar.first, min(universalBitWidth, bitSize), approximationType);
        }
        else
        {
            return vars.at(bVar.first);
        }
    }
    else if (e.is_numeral())
    {
	return getNumeralBvec(e);
    }
    else if (e.is_const())
    {
	stringstream ss;
	ss << e;

	if (exisentialBitWidth != 0)
	{
	    int bitSize = e.get_sort().bv_size();
	    return getApproximatedVariable(ss.str(), min(exisentialBitWidth, bitSize), approximationType);
	}
	else
	{
	    return vars.at(ss.str());
	}
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	string functionName = f.name().str();

	if (functionName == "bvadd")
	{
	    Bvec toReturn = getBvecFromExpr(e.arg(0), boundVars);
	    for (unsigned int i = 1; i < num; i++)
	    {
		toReturn = toReturn + getBvecFromExpr(e.arg(i), boundVars);
	    }

	    bvecExprCache.insert({(Z3_ast)e, {toReturn, boundVars}});
	    return toReturn;
	}
	else if (functionName == "bvsub")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvsub -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    Bvec result = getBvecFromExpr(e.arg(0), boundVars) - getBvecFromExpr(e.arg(1), boundVars);

	    bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvshl")
	{
	    if (e.arg(1).is_numeral())
	    {
		Bvec result = getBvecFromExpr(e.arg(0), boundVars) << getNumeralValue(e.arg(1));

		bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
		return result;
	    }
	    else
	    {
		Bvec result = getBvecFromExpr(e.arg(0), boundVars) << getBvecFromExpr(e.arg(1), boundVars);

		bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
		return result;
	    }
	}
	else if (functionName == "bvlshr")
	{
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

	    Bvec arg0Reversed = Bvec::bvec_false(bddManager, arg0.bitnum());
	    for (uint i = 0; i < arg0.bitnum(); i++)
	    {
		arg0Reversed.set(i, arg0[arg0.bitnum() - i - 1]);
	    }

	    Bvec resultReversed = arg0Reversed << arg1;

	    Bvec result = Bvec::bvec_false(bddManager, resultReversed.bitnum());
	    for (uint i = 0; i < resultReversed.bitnum(); i++)
	    {
		result.set(i, resultReversed[resultReversed.bitnum() - i - 1]);
	    }

	    return result;
	}
	else if (functionName == "bvashr")
	{
	    if (e.arg(1).is_numeral())
	    {
		Bvec leftBV = getBvecFromExpr(e.arg(0), boundVars);
		Bvec result = leftBV.bvec_shrfixed(getNumeralValue(e.arg(1)),
						   leftBV[e.num_args() - 1]);

		bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
		return result;
	    }
	    else
	    {
		Bvec leftBV = getBvecFromExpr(e.arg(0), boundVars);
		Bvec result = Bvec::bvec_shr(leftBV,
					     getBvecFromExpr(e.arg(1), boundVars),
					     leftBV[e.num_args() - 1]);
		bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
		return result;
	    }
	}
	else if (functionName == "zero_extend")
	{
	    Z3_func_decl z3decl = (Z3_func_decl)e.decl();
	    int bitsExtend = Z3_get_decl_int_parameter(*context, z3decl, 0);

	    int totalBits = bitsExtend + f.domain(0).bv_size();

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    Bvec result = arg0.bvec_coerce(totalBits);

	    return result;
	}
	else if (functionName == "concat")
	{
	    int newSize = f.range().bv_size();
	    int offset = 0;

	    Bvec currentBvec = Bvec::bvec_false(bddManager, newSize);
	    assert(num > 0);
	    for (int i = num-1; i >= 0; i--)
	    {
		auto arg = getBvecFromExpr(e.arg(i), boundVars);
		currentBvec = Bvec::bvec_map2(currentBvec,
					      arg.bvec_coerce(newSize) << offset,
					      [&](const BDD &a, const BDD &b) { return a ^ b; });
		offset += f.domain(i).bv_size();
	    }

	    Bvec result = currentBvec;
	    return result;
	}
	else if (functionName == "extract")
	{
	    Z3_func_decl z3decl = (Z3_func_decl)e.decl();

	    int bitTo = Z3_get_decl_int_parameter(*context, z3decl, 0);
	    int bitFrom = Z3_get_decl_int_parameter(*context, z3decl, 1);

	    int extractBits = bitTo - bitFrom + 1;

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    Bvec result = arg0.bvec_shrfixed(bitFrom, bddManager.bddZero()).bvec_coerce(extractBits);

	    bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvnot")
	{
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    Bvec result = Bvec::bvec_map1(arg0,
					  [&](const BDD &a) { return !a; });

	    return result;
	}
	else if (functionName == "bvneg")
	{
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);

	    Bvec result = bvneg(arg0, e.arg(0).get_sort().bv_size());
	    return result;
	}
	else if (functionName == "bvor")
	{
	    Bvec toReturn = getBvecFromExpr(e.arg(0), boundVars);
	    for (unsigned int i = 1; i < num; i++)
	    {
		toReturn = Bvec::bvec_map2(toReturn,
					   getBvecFromExpr(e.arg(i), boundVars),
					   [&](const BDD &a, const BDD &b) { return a + b; });
	    }

	    bvecExprCache.insert({(Z3_ast)e, {toReturn, boundVars}});
	    return toReturn;
	}
	else if (functionName == "bvand")
	{
	    Bvec toReturn = getBvecFromExpr(e.arg(0), boundVars);
	    for (unsigned int i = 1; i < num; i++)
	    {
		toReturn = Bvec::bvec_map2(toReturn,
					   getBvecFromExpr(e.arg(i), boundVars),
					   [&](const BDD &a, const BDD &b) { return a * b; });
	    }

	    bvecExprCache.insert({(Z3_ast)e, {toReturn, boundVars}});
	    return toReturn;
	}
	else if (functionName == "bvxor")
	{
	    Bvec toReturn = getBvecFromExpr(e.arg(0), boundVars);
	    for (unsigned int i = 1; i < num; i++)
	    {
		toReturn = Bvec::bvec_map2(toReturn,
					   getBvecFromExpr(e.arg(i), boundVars),
					   [&](const BDD &a, const BDD &b) { return a ^ b; });
	    }

	    bvecExprCache.insert({(Z3_ast)e, {toReturn, boundVars}});
	    return toReturn;
	}
	else if (functionName == "bvmul")
	{
	    if (e.num_args() != 2)
	    {
		Bvec toReturn = getBvecFromExpr(e.arg(0), boundVars);
		for (unsigned int i = 1; i < num; i++)
		{
		    toReturn = toReturn * getBvecFromExpr(e.arg(i), boundVars);
		    toReturn = toReturn.bvec_coerce(e.decl().range().bv_size());
		}

		bvecExprCache.insert({(Z3_ast)e, {toReturn, boundVars}});
		return toReturn;
	    }

	    if (m_negateMul)
	    {
		if (e.arg(0).is_numeral())
		{
		    int ones = getNumeralOnes(e.arg(0));

		    if ((2U * ones) > e.arg(0).get_sort().bv_size())
		    {
			expr expr(*context);

			if (e.arg(1).is_const() || e.arg(1).is_var())
			{
			    expr = -e.arg(0) * -e.arg(1);
			}
			else
			{
			    expr = -(-e.arg(0) * e.arg(1));
			}

			bvecExprCache.clear();
			bddExprCache.clear();
			return getBvecFromExpr(expr, boundVars);
		    }
		}
	    }

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

	    Bvec result(bddManager);

	    if (arg1.bvec_isConst())
	    {
		swap(arg0,arg1);
	    }

	    if (arg0.bitnum() <= 32 && arg0.bvec_isConst())
	    {
		unsigned int val = arg0.bvec_val();

		if (val <= INT_MAX)
		{
		    result = arg1 * val;
		    bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
		    return result;
		}
	    }

	    result = (arg0 * arg1).bvec_coerce(e.decl().range().bv_size());
	    bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvurem_i" || functionName == "bvurem")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvurem_i -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    Bvec div = Bvec::bvec_false(bddManager, e.decl().range().bv_size());
	    Bvec rem = Bvec::bvec_false(bddManager, e.decl().range().bv_size());

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

	    int result = arg0.bvec_div(arg0, arg1, div, rem);
	    std::cout << result << std::endl;
	    if (result == 0)
	    {
		Bvec result = rem;
		bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
		return result;
	    }
	    else
	    {
		cout << "ERROR: division error" << endl;
		cout << "unknown";
		exit(0);
	    }
	}
	else if (functionName == "bvudiv_i" || functionName == "bvudiv")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvudiv_i -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    Bvec div = Bvec::bvec_false(bddManager, e.decl().range().bv_size());
	    Bvec rem = Bvec::bvec_false(bddManager, e.decl().range().bv_size());

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

	    int result = arg0.bvec_div(arg0, arg1, div, rem);
	    if (result == 0)
	    {
		Bvec result = div;
		bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
		return result;
	    }
	    else
	    {
		std::cout << e << std::endl;
		std::cout << "l:" << arg0.bitnum() << ", r:" << arg1.bitnum() << std::endl;

		cout << "ERROR: division error" << endl;
		cout << "unknown";
		exit(0);
	    }
	}
	else if (functionName == "bvsdiv_i" || functionName == "bvsdiv")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvudiv_i -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    expr arg0 = e.arg(0);
	    expr arg1 = e.arg(1);

	    expr zero = context->bv_val(0, 1);
	    expr one = context->bv_val(1, 1);

	    int size = e.arg(0).get_sort().bv_size();
	    expr msb_s = arg0.extract(size-1, size-1);
	    expr msb_t = arg1.extract(size-1, size-1);

	    expr e = ite(msb_s == zero && msb_t == zero,
			 udiv(arg0, arg1),
			 ite (msb_s == one && msb_t == zero,
			      -udiv(-arg0, arg1),
			      ite (msb_s == zero && msb_t == one,
				   -udiv(arg0, -arg1),
				   udiv(-arg0, -arg1))));

	    bddExprCache.clear();
	    bvecExprCache.clear();

	    Bvec result = getBvecFromExpr(e, boundVars);

	    bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "bvsrem_i" || functionName == "bvsrem")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvsrem_i -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    expr arg0 = e.arg(0);
	    expr arg1 = e.arg(1);

	    expr zero = context->bv_val(0, 1);
	    expr one = context->bv_val(1, 1);

	    int size = e.arg(0).get_sort().bv_size();
	    expr msb_s = arg0.extract(size-1, size-1);
	    expr msb_t = arg1.extract(size-1, size-1);

	    expr e = ite(msb_s == zero && msb_t == zero,
			 urem(arg0, arg1),
			 ite (msb_s == one && msb_t == zero,
			      -urem(-arg0, arg1),
			      ite (msb_s == zero && msb_t == one,
				   urem(arg0, -arg1),
				   -urem(-arg0, -arg1))));

	    bddExprCache.clear();
	    bvecExprCache.clear();

	    Bvec result = getBvecFromExpr(e, boundVars);

	    bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else if (functionName == "if")
	{
	    if (e.num_args() != 3)
	    {
		std::cout << "if -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
	    auto arg2 = getBvecFromExpr(e.arg(2), boundVars);

	    Bvec result = Bvec::bvec_map2(arg1, arg2, [&](const BDD &a, const BDD &b) { return arg0.Ite(a, b); });

	    bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
	    return result;
	}
	else
	{
	    cout << "ERROR: not supported function " << functionName << endl;
	    cout << "unknown";
	    exit(0);
	}
    }

    cout << "bvec else" << e << endl;
    abort();
}

unsigned int ExprToBDDTransformer::getNumeralValue(const expr &e)
{
    std::stringstream ss;
    ss << e;
    return HexHelper::get_numeral_value(ss.str());
}

unsigned int ExprToBDDTransformer::getNumeralOnes(const expr &e)
{
    std::stringstream ss;
    ss << e;
    return HexHelper::numeral_get_bin_zeroes(ss.str());
}

Bvec ExprToBDDTransformer::getNumeralBvec(const z3::expr &e)
{
    z3::sort s = e.get_sort();

    std::stringstream ss;
    ss << e;

    string numeralString = ss.str();

    int bitSize = s.bv_size();

    const string prefix = numeralString.substr(0, 2);
    string valueString = numeralString.substr(2);

    assert(prefix == "#x" || prefix == "#b");

    Bvec toReturn = Bvec::bvec_false(bddManager, bitSize);
    if (prefix == "#x")
    {
	valueString = HexHelper::hex_str_to_bin_str(valueString);
    }

    int i = valueString.size();
    for (const char& c : valueString)
    {
	i--;
	toReturn.set(i, c == '1' ? bddManager.bddOne() : bddManager.bddZero());
    }

    return toReturn;
}

BDD ExprToBDDTransformer::Proccess()
{
    exisentialBitWidth = 0;
    universalBitWidth = 0;

    std::stringstream ss;
    ss << expression;
    if (ss.str() == "true")
    {
        return bddManager.bddOne();
    }
    else if (ss.str() == "false")
    {
        return bddManager.bddZero();
    }

    return loadBDDsFromExpr(expression);
}

BDD ExprToBDDTransformer::ProcessUnderapproximation(int bitWidth)
{
    exisentialBitWidth = bitWidth;
    universalBitWidth = 0;

    return loadBDDsFromExpr(expression);
}

BDD ExprToBDDTransformer::ProcessOverapproximation(int bitWidth)
{
    universalBitWidth = bitWidth;
    exisentialBitWidth = 0;

    return loadBDDsFromExpr(expression);
}
