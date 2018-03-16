#include "ExprToBDDTransformer.h"
#include <cmath>
#include <iostream>
#include <sstream>
#include <list>
#include <algorithm>

#include "HexHelper.h"
#include "Solver.h"

#define DEBUG false

const unsigned int precisionMultiplier = 1000;

Bvec ExprToBDDTransformer::bvneg(Bvec bv, int bitSize)
{
    return Bvec::bvec_map1(bv, [&](const MaybeBDD &a) { return !a; }) + Bvec::bvec_con(bddManager, bitSize, 1);
}

using namespace std;
using namespace z3;

ExprToBDDTransformer::ExprToBDDTransformer(z3::context &ctx, z3::expr e, Config config) : config(config), expression(e)
{
    this->context = &ctx;
    bddManager = Cudd();
    configureReorder();

    m_dontCare = bddManager.bddZero();
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
	std::unique_lock<std::mutex> lk(Solver::m_z3context);
	std::string expressionString = e.to_string();

	if (expressionString == "true" || expressionString == "false")
	{
	    return;
	}

	int bitWidth = e.get_sort().is_bool() ? 1 : e.get_sort().bv_size();
	constSet.insert(make_pair(expressionString, bitWidth));
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
		std::unique_lock<std::mutex> lk(Solver::m_z3context);
                var c = make_pair(e.to_string(), 1);
		lk.unlock();
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

    if (config.initialOrder == HEURISTIC)
    {
        orderer.OrderFor(expression);
    }
    else if (config.initialOrder == INTERLEAVE_ALL)
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
	    if (DEBUG)
	    {
		cout << "Var: " << v.first << endl;
	    }
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

    if (lastBW != variableBitWidth)
    {
	//sameBWPreciseBdds.clear();
	sameBWPreciseBvecs.clear();
	lastBW = variableBitWidth;
    }

    this->expression = e;
    variableApproximationHappened = false;
    auto result = getBDDFromExpr(e, {}, true, true);

    operationApproximationHappened = !result.IsPrecise();


    //bddManager.info();

    bddExprCache.clear();
    bvecExprCache.clear();

    if (approximation == OVERAPPROXIMATION)
    {
	return result.upper;
    }

    return result.lower;
}

BDDInterval ExprToBDDTransformer::getConjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars, bool onlyExistentials, bool isPositive)
{
    vector<BDDInterval> results;

    for (unsigned int i = 0; i < arguments.size(); i++)
    {
        auto argBdd = getBDDFromExpr(arguments[i], boundVars, onlyExistentials, isPositive);

        if (argBdd.upper.IsZero())
        {
            return argBdd;
        }
        else
        {
            results.push_back(argBdd);
        }
    }

    if (results.size() == 0)
    {
	return BDDInterval{ bddManager.bddOne()};
    }
    else
    {
	std::sort(results.begin(), results.end(),
		  [&](const auto a, const auto b) -> bool
		  {
		      return bddManager.nodeCount(std::vector<BDD>{a.upper}) < bddManager.nodeCount(std::vector<BDD>{b.upper});
		  });

	auto toReturn = results.at(0);

	for (unsigned int i = 1; i < results.size(); i++)
	{
	    if (toReturn.upper.IsZero())
	    {
		return BDDInterval{bddManager.bddZero()};
	    }

	    toReturn = toReturn * results.at(i);
	}

	return toReturn;
    }
}

BDDInterval ExprToBDDTransformer::getDisjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars, bool onlyExistentials, bool isPositive)
{
    vector<BDDInterval> results;

    for (unsigned int i = 0; i < arguments.size(); i++)
    {
        auto argBdd = getBDDFromExpr(arguments[i], boundVars, onlyExistentials, isPositive);

	if (argBdd.lower.IsOne())
        {
            return argBdd;
        }
	else
	{
	    results.push_back(argBdd);
	}
    }

    if (results.size() == 0)
    {
	return BDDInterval{bddManager.bddZero()};
    }
    else
    {
	std::sort(results.begin(), results.end(),
		  [&](const auto a, const auto b) -> bool
		  {
		      return bddManager.nodeCount(std::vector<BDD>{a.lower}) < bddManager.nodeCount(std::vector<BDD>{b.lower});
		  });

	auto toReturn = results.at(0);

	for (unsigned int i = 1; i < results.size(); i++)
	{
	    if (toReturn.lower.IsOne())
	    {
		return BDDInterval{bddManager.bddOne()};
	    }

	    toReturn = toReturn + results.at(i);
	}

	return toReturn;
    }
}

bool ExprToBDDTransformer::correctBoundVars(const std::vector<boundVar> &boundVars, const std::vector<boundVar> &cachedBoundVars) const
{
    if (boundVars.size() > cachedBoundVars.size())
    {
	return false;
    }

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

BDDInterval ExprToBDDTransformer::getBDDFromExpr(const expr &e, const vector<boundVar>& boundVars, bool onlyExistentials, bool isPositive)
{
    assert(e.is_bool());

    auto item = bddExprCache.find((Z3_ast)e);
    if (item != bddExprCache.end())
    {
        if (correctBoundVars(boundVars, (item->second).second))
        {
            return (item->second).first;
        }
    }

    // auto preciseItem = preciseBdds.find((Z3_ast)e);
    // if (preciseItem != preciseBdds.end())
    // {
    //     if (correctBoundVars(boundVars, (preciseItem->second).second))
    //     {
    // 	    //std::cout << "PRECISE :" << e << std::endl;
    //         return {(preciseItem->second).first, PRECISE};
    //     }
    // }

    // auto sameBWitem = sameBWPreciseBdds.find((Z3_ast)e);
    // if (sameBWitem != sameBWPreciseBdds.end())
    // {
    //     if (correctBoundVars(boundVars, (sameBWitem->second).second))
    //     {
    //         return (sameBWitem->second).first;
    //     }
    // }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];
        return BDDInterval{vars.at(bVar.first) == Bvec::bvec_true(bddManager, 1)};
    }
    else if (e.is_const())
    {
	if (e.is_app() && e.decl().decl_kind() == Z3_OP_TRUE)
	{
	    return BDDInterval{bddManager.bddOne()};
	}
	else if (e.is_app() && e.decl().decl_kind() == Z3_OP_FALSE)
	{
	    return BDDInterval{bddManager.bddZero()};
	}

	Solver::m_z3context.lock();
	std::string exprString = e.to_string();
	Solver::m_z3context.unlock();

	return insertIntoCaches(e, BDDInterval{vars.at(exprString) == Bvec::bvec_true(bddManager, 1)}, boundVars);
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
	    BDDInterval result;

	    assert(sort.is_bv() || sort.is_bool());
	    if (sort.is_bv())
	    {
		MaybeBDD::ResetApproximationFlag();
		if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)
		{
		    auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
		    auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

		    if (isPositive)
		    {
			return BDDInterval{Bvec::bvec_equ_overApprox(arg0, arg1),
				Bvec::bvec_equ_underApprox(arg0, arg1)};
		    }
		    else
		    {
			return BDDInterval{Bvec::bvec_equ_underApprox(arg0, arg1),
				Bvec::bvec_equ_overApprox(arg0, arg1)};
		    }
		}
		else
		{
		    result = BDDInterval(Bvec::bvec_equ(getBvecFromExpr(e.arg(0), boundVars).value,
							getBvecFromExpr(e.arg(1), boundVars).value));
		}
	    }
	    else if (sort.is_bool())
	    {
		result = getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, isPositive).Xnor(
		    getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, isPositive));
	    }

	    return insertIntoCaches(e, result, boundVars);
	}
	else if (functionName == "not")
	{
	    return !getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, !isPositive);
	}
	else if (functionName == "and")
	{
	    vector<expr> arguments;

	    for (unsigned int i = 0; i < num; i++)
	    {
		arguments.push_back(e.arg(i));
	    }

	    auto result = getConjunctionBdd(arguments, boundVars, onlyExistentials, isPositive);
	    return insertIntoCaches(e, result, boundVars);
	}
	else if (functionName == "or")
	{
	    vector<expr> arguments;
	    for (unsigned int i = 0; i < num; i++)
	    {
		arguments.push_back(e.arg(i));
	    }

	    auto result = getDisjunctionBdd(arguments, boundVars, onlyExistentials, isPositive);
	    return insertIntoCaches(e, result, boundVars);
	}
	else if (functionName == "=>")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "=> -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto result = !getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, !isPositive) +
		getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, isPositive);
	    return insertIntoCaches(e, result, boundVars);
	}
	else if (functionName == "bvule")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvule -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result;
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

	    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)
	    {
		auto over = Bvec::bvec_lte_overApprox(arg0, arg1);
		auto under = Bvec::bvec_lte_underApprox(arg0, arg1) |
		    Bvec::bvec_equ_underApprox(arg0, Bvec::bvec_false(bddManager, arg0.bitnum())) |
		    Bvec::bvec_equ_underApprox(arg1, Bvec::bvec_true(bddManager, arg1.bitnum()));

		return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
	    }
	    else
	    {
		result = Bvec::bvec_lte(arg0, arg1);
	    }

	    return insertIntoCaches(e, BDDInterval{result}, boundVars);
	}
	else if (functionName == "bvult")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvult -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result;
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

	    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)
	    {
		auto over = Bvec::bvec_lth_overApprox(arg0, arg1) &
		    Bvec::bvec_nequ_overApprox(arg0, Bvec::bvec_true(bddManager, arg0.bitnum())) &
		    Bvec::bvec_nequ_overApprox(arg1, Bvec::bvec_false(bddManager, arg1.bitnum()));
		auto under = Bvec::bvec_lth_underApprox(arg0, arg1);

		return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
	    }
	    else
	    {
		result = Bvec::bvec_lth(arg0, arg1);
	    }

	    return insertIntoCaches(e, BDDInterval{result}, boundVars);
	}
	else if (functionName == "bvuge")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvugr -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result;
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

	    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)
	    {
		auto over = Bvec::bvec_lte_overApprox(arg1, arg0);
		auto under = Bvec::bvec_lte_underApprox(arg1, arg0) |
		    Bvec::bvec_equ_underApprox(arg1, Bvec::bvec_false(bddManager, arg1.bitnum())) |
		    Bvec::bvec_equ_underApprox(arg0, Bvec::bvec_true(bddManager, arg0.bitnum()));

		return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
	    }
	    else
	    {
		result = Bvec::bvec_lte(arg1, arg0);
	    }

	    return insertIntoCaches(e, BDDInterval{result}, boundVars);
	}
	else if (functionName == "bvugt")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvugt -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result;
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

	    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)
	    {
		auto over = Bvec::bvec_lth_overApprox(arg1, arg0) &
		    Bvec::bvec_nequ_overApprox(arg1, Bvec::bvec_true(bddManager, arg1.bitnum())) &
		    Bvec::bvec_nequ_overApprox(arg0, Bvec::bvec_false(bddManager, arg0.bitnum()));
		auto under = Bvec::bvec_lth_underApprox(arg1, arg0);

		return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
	    }
	    else
	    {
		result = Bvec::bvec_lth(arg1, arg0);
	    }

	    return insertIntoCaches(e, BDDInterval{result}, boundVars);
	}
	else if (functionName == "bvsle")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvsle -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result;
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

	    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)
	    {
		auto over = Bvec::bvec_slte_overApprox(arg0, arg1);

		Bvec leastNumber = Bvec::bvec_false(bddManager, arg0.bitnum());
		leastNumber.set(arg0.bitnum() - 1, MaybeBDD(bddManager, bddManager.bddOne()));

		Bvec greatestNumber = Bvec::bvec_true(bddManager, arg0.bitnum());
		greatestNumber.set(arg0.bitnum() - 1, MaybeBDD(bddManager, bddManager.bddZero()));
		auto under = Bvec::bvec_slte_underApprox(arg0, arg1) |
		    Bvec::bvec_equ_underApprox(arg0, leastNumber) |
		    Bvec::bvec_equ_underApprox(arg1, greatestNumber);

		return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
	    }
	    else
	    {
		result = Bvec::bvec_slte(arg0, arg1);
	    }

	    return insertIntoCaches(e, BDDInterval{result}, boundVars);
	}
	else if (functionName == "bvslt")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvslt -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    BDD result;
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars).value;
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;

	    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)
	    {
		Bvec leastNumber = Bvec::bvec_false(bddManager, arg0.bitnum());
		leastNumber.set(arg0.bitnum() - 1, MaybeBDD(bddManager, bddManager.bddOne()));

		Bvec greatestNumber = Bvec::bvec_true(bddManager, arg0.bitnum());
		greatestNumber.set(arg0.bitnum() - 1, MaybeBDD(bddManager, bddManager.bddZero()));

		auto over = Bvec::bvec_slth_overApprox(arg0, arg1) &
		    Bvec::bvec_nequ_overApprox(arg0, greatestNumber) &
		    Bvec::bvec_nequ_overApprox(arg1, leastNumber);
		auto under = Bvec::bvec_slth_underApprox(arg0, arg1);

		return isPositive ? BDDInterval(over, under) : BDDInterval(under, over);
	    }
	    else
	    {
		result = Bvec::bvec_slth(arg0, arg1);
	    }

	    return insertIntoCaches(e, BDDInterval{result}, boundVars);
	}
	else if (functionName == "iff")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "iff -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto arg0 = getBDDFromExpr(e.arg(0), boundVars, false, isPositive);
	    auto arg1 = getBDDFromExpr(e.arg(1), boundVars, false, isPositive);

	    auto result = arg0.Xnor(arg1);
	    return insertIntoCaches(e, result, boundVars);
	}
	else if (functionName == "if")
	{
	    if (e.num_args() != 3)
	    {
		std::cout << "if -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto arg0 = getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, isPositive);
	    auto arg1 = getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, isPositive);
	    auto arg2 = getBDDFromExpr(e.arg(2), boundVars, onlyExistentials, isPositive);

	    auto result = arg0.Ite(arg1, arg2);

	    return insertIntoCaches(e, result, boundVars);
	}
	else
	{
	    cout << "function " << f.name().str() << endl;
	    exit(1);
	}
    }
    else if(e.is_quantifier())
    {
	Z3_ast ast = (Z3_ast)e;

	int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

	auto newBoundVars = boundVars;
	for (int i = 0; i < boundVariables; i++)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    BoundType bt = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;
	    newBoundVars.push_back(std::pair<string, BoundType>(current_symbol.str(), bt));
	}

	BDDInterval bodyBdd;
	if (onlyExistentials)
	{
	    if (Z3_is_quantifier_forall(*context, ast))
	    {
		//only existentials so far, but this one is universal
		bodyBdd = getBDDFromExpr(e.body(), newBoundVars, false, isPositive);
	    }
	    else
	    {
		//only existentials so far and this one is also existential
		return getBDDFromExpr(e.body(), newBoundVars, true, isPositive);
	    }
	}
	else
	{
	    bodyBdd = getBDDFromExpr(e.body(), newBoundVars, false, isPositive);
	}

	for (int i = boundVariables - 1; i >= 0; i--)
	{
	    Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
	    symbol current_symbol(*context, z3_symbol);

	    auto varSet = varSets.at(current_symbol.str());
	    if (Z3_is_quantifier_forall(*context, ast))
	    {
		bodyBdd = bodyBdd.UnivAbstract(varSet);
	    }
	    else
	    {
		bodyBdd = bodyBdd.ExistAbstract(varSet);
	    }
	}

	return insertIntoCaches(e, bodyBdd, boundVars);
    }

    cout << "bdd else: " << e << endl;
    abort();
}

Approximated<Bvec> ExprToBDDTransformer::getApproximatedVariable(const std::string& varName, int newBitWidth, const ApproximationType& at)
{
    Bvec var = vars.at(varName);
    variableApproximationHappened = true;

    if (newBitWidth > 0)
    {
	newBitWidth = min(newBitWidth, (int)var.bitnum());
	for (unsigned int i = newBitWidth; i < var.bitnum(); i++)
	{
	    if (at == ZERO_EXTEND && (i != var.bitnum() - 1 || newBitWidth == 1))
	    {
		var.set(i, bddManager.bddZero());
	    }
	    else if (at == SIGN_EXTEND)
	    {
		var.set(i, var[i - 1]);
	    }
	}

	return {var, PRECISE, APPROXIMATED};
    }
    else
    {
	newBitWidth = min(-newBitWidth, (int)var.bitnum());
	for (int i = var.bitnum() - newBitWidth - 1; i >= 0; i--)
	{
	    if (at == ZERO_EXTEND && (i != 0  || newBitWidth == 1))
	    {
		var.set(i, bddManager.bddZero());
	    }
	    else if (at == SIGN_EXTEND)
	    {
		var.set(i, var[i + 1]);
	    }
	}

	return {var, PRECISE, APPROXIMATED};
    }
}

Approximated<Bvec> ExprToBDDTransformer::getBvecFromExpr(const expr &e, const vector<boundVar>& boundVars)
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

    auto preciseItem = preciseBvecs.find((Z3_ast)e);
    if (preciseItem != preciseBvecs.end())
    {
        if (correctBoundVars(boundVars, (preciseItem->second).second))
        {
            //return {(preciseItem->second).first, PRECISE};
        }
    }

    auto sameBWitem = sameBWPreciseBvecs.find((Z3_ast)e);
    if (sameBWitem != sameBWPreciseBvecs.end())
    {
        if (correctBoundVars(boundVars, (sameBWitem->second).second))
        {
            return (sameBWitem->second).first;
        }
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];

	if (config.approximationMethod == VARIABLES || config.approximationMethod == BOTH)
	{
	    if (bVar.second == EXISTENTIAL && approximation == UNDERAPPROXIMATION)
	    {
		return getApproximatedVariable(bVar.first, variableBitWidth, approximationType);
	    }
	    if (bVar.second == UNIVERSAL && approximation == OVERAPPROXIMATION)
	    {
		return getApproximatedVariable(bVar.first, variableBitWidth, approximationType);
	    }
	}

	Approximated<Bvec> result = {vars.at(bVar.first), PRECISE};
	return insertIntoCaches(e, result, boundVars);
    }
    else if (e.is_numeral())
    {
	return insertIntoCaches(e, {getNumeralBvec(e), PRECISE}, boundVars);
    }
    else if (e.is_const())
    {
	Bvec result(bddManager);

	if ((config.approximationMethod == VARIABLES || config.approximationMethod == BOTH) && approximation == UNDERAPPROXIMATION)
	{
	    std::unique_lock<std::mutex> lk(Solver::m_z3context);
	    auto result = getApproximatedVariable(e.to_string(), variableBitWidth, approximationType);
	    return insertIntoCaches(e, result, boundVars);
	}
	else
	{
	    std::unique_lock<std::mutex> lk(Solver::m_z3context);
	    return insertIntoCaches(e, {vars.at(e.to_string()), PRECISE}, boundVars);
	}
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	string functionName = f.name().str();

	if (functionName == "bvadd")
	{
	    //std::cout << e << std::endl;
	    auto toReturn = getBvecFromExpr(e.arg(0), boundVars);
	    for (unsigned int i = 1; i < num; i++)
	    {
		if ((config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) &&
		    operationPrecision != 0)
		{
		    if (config.limitBddSizes)
		    {
			toReturn = toReturn.Apply2<Bvec>(getBvecFromExpr(e.arg(i), boundVars),
							 [&] (auto x, auto y) {
							     return Bvec::bvec_add_nodeLimit(x, y, 2*precisionMultiplier*operationPrecision);
							 });
		    }
		    else
		    {
			toReturn = toReturn.Apply2<Bvec>(getBvecFromExpr(e.arg(i), boundVars),
							 [&] (auto x, auto y) {
							     return Bvec::bvec_add(x, y, operationPrecision);
							 });
		    }
		}
		else
		{
		    toReturn = toReturn.Apply2<Bvec>(getBvecFromExpr(e.arg(i), boundVars),
						     [&] (auto x, auto y) {
							 return x + y;
						     });
		}
	    }

	    if (toReturn.operationPrecision == PRECISE && toReturn.variablePrecision == PRECISE)
	    {
		preciseBvecs.insert({(Z3_ast)e, {toReturn.value, boundVars}});
	    }

	    return insertIntoCaches(e, toReturn, boundVars);
	}
	else if (functionName == "bvsub")
	{
	    if (e.num_args() != 2)
	    {
		std::cout << "bvsub -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    auto result = getBvecFromExpr(e.arg(0), boundVars).Apply2<Bvec>(
		getBvecFromExpr(e.arg(1), boundVars),
		[] (auto x, auto y) {
		    return x - y;
		});

	    return insertIntoCaches(e, result, boundVars);
	}
	else if (functionName == "bvshl")
	{
	    if (e.arg(1).is_numeral())
	    {
		auto result = getBvecFromExpr(e.arg(0), boundVars).Apply<Bvec>(
		    [&] (auto x) {
			return x << getNumeralValue(e.arg(1));
		    });

		return insertIntoCaches(e, result, boundVars);
	    }
	    else
	    {
		auto result = getBvecFromExpr(e.arg(0), boundVars).Apply2<Bvec>(
		    getBvecFromExpr(e.arg(1), boundVars),
		    [] (auto x, auto y) {
			return x << y;
		    });
		return insertIntoCaches(e, result, boundVars);
	    }
	}
	else if (functionName == "bvlshr")
	{
	    auto [arg0, arg0OpPrecision, arg0VarPrecision] = getBvecFromExpr(e.arg(0), boundVars);
	    auto [arg1, arg1OpPrecision, arg1VarPrecision] = getBvecFromExpr(e.arg(1), boundVars);

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

	    return insertIntoCaches(e, {result, arg0OpPrecision && arg1OpPrecision, arg0VarPrecision && arg1VarPrecision}, boundVars);
	}
	else if (functionName == "bvashr")
	{
	    if (e.arg(1).is_numeral())
	    {
		auto [leftBV, opPrecision, varPrecision] = getBvecFromExpr(e.arg(0), boundVars);
		Bvec result = leftBV.bvec_shrfixed(getNumeralValue(e.arg(1)),
						   leftBV[e.num_args() - 1]);

		return insertIntoCaches(e, {result, opPrecision, varPrecision}, boundVars);
	    }
	    else
	    {
		auto leftBV = getBvecFromExpr(e.arg(0), boundVars);

		auto result = leftBV.Apply2<Bvec>(
		    getBvecFromExpr(e.arg(1), boundVars),
		    [&] (auto x, auto y) {
			return Bvec::bvec_shr(x, y, leftBV.value[e.num_args() - 1]);
		    });

		return insertIntoCaches(e, result, boundVars);
	    }
	}
	else if (functionName == "zero_extend")
	{
	    Z3_func_decl z3decl = (Z3_func_decl)e.decl();
	    int bitsExtend = Z3_get_decl_int_parameter(*context, z3decl, 0);

	    int totalBits = bitsExtend + f.domain(0).bv_size();

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);

	    auto result = arg0.Apply<Bvec>(
		[&] (auto x) {
		    return x.bvec_coerce(totalBits);
		});

	    return result;
	}
	else if (functionName == "concat")
	{
	    int newSize = f.range().bv_size();
	    int offset = 0;

	    auto currentBvec = Bvec::bvec_false(bddManager, newSize);
	    Precision opPrecision = PRECISE;
	    Precision varPrecision = PRECISE;

	    assert(num > 0);
	    for (int i = num-1; i >= 0; i--)
	    {
		auto [arg, argOpPrecision, argVarPrecision] = getBvecFromExpr(e.arg(i), boundVars);
		currentBvec = Bvec::bvec_map2(currentBvec,
					      arg.bvec_coerce(newSize) << offset,
					      [&](const MaybeBDD &a, const MaybeBDD &b) { return a ^ b; });
		opPrecision = opPrecision && argOpPrecision;
		varPrecision = varPrecision && argVarPrecision;
		offset += f.domain(i).bv_size();
	    }

	    return insertIntoCaches(e, {currentBvec, opPrecision, varPrecision}, boundVars);
	}
	else if (functionName == "extract")
	{
	    Z3_func_decl z3decl = (Z3_func_decl)e.decl();

	    int bitTo = Z3_get_decl_int_parameter(*context, z3decl, 0);
	    int bitFrom = Z3_get_decl_int_parameter(*context, z3decl, 1);

	    int extractBits = bitTo - bitFrom + 1;

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);

	    auto result = arg0.Apply<Bvec>(
		[&] (auto x) {
		    return x.bvec_shrfixed(bitFrom, MaybeBDD(bddManager, bddManager.bddZero()))
		    .bvec_coerce(extractBits);
		});

	    return insertIntoCaches(e, result, boundVars);
	}
	else if (functionName == "bvnot")
	{
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);

	    return arg0.Apply<Bvec>(
		[&] (auto x) {
		    return Bvec::bvec_map1(x, [&](const MaybeBDD &a) { return !a; });
		});
	}
	else if (functionName == "bvneg")
	{
	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);

	    return arg0.Apply<Bvec>(
		[&] (auto x) {
		    return bvneg(x, e.arg(0).get_sort().bv_size());
		});
	}
	else if (functionName == "bvor")
	{
	    auto toReturn = getBvecFromExpr(e.arg(0), boundVars);
	    for (unsigned int i = 1; i < num; i++)
	    {
		toReturn = toReturn.Apply2<Bvec>(getBvecFromExpr(e.arg(i), boundVars),
						 [] (auto x, auto y) {
						     return Bvec::bvec_map2(x, y,
									    [&](const MaybeBDD &a, const MaybeBDD &b) { return a + b; }); });
	    }

	    return insertIntoCaches(e, toReturn, boundVars);
	}
	else if (functionName == "bvand")
	{
	    auto toReturn = getBvecFromExpr(e.arg(0), boundVars);
	    for (unsigned int i = 1; i < num; i++)
	    {
		toReturn = toReturn.Apply2<Bvec>(getBvecFromExpr(e.arg(i), boundVars),
						 [] (auto x, auto y) {
						     return Bvec::bvec_map2(x, y,
									    [&](const MaybeBDD &a, const MaybeBDD &b) { return a * b; }); });
	    }

	    bvecExprCache.insert({(Z3_ast)e, {toReturn, boundVars}});
	    return toReturn;
	}
	else if (functionName == "bvxor")
	{
	    auto toReturn = getBvecFromExpr(e.arg(0), boundVars);
	    for (unsigned int i = 1; i < num; i++)
	    {
		toReturn = toReturn.Apply2<Bvec>(getBvecFromExpr(e.arg(i), boundVars),
						 [] (auto x, auto y) {
						     return Bvec::bvec_map2(x, y,
									    [&](const MaybeBDD &a, const MaybeBDD &b) { return a ^ b; }); });
	    }

	    return insertIntoCaches(e, toReturn, boundVars);
	}
	else if (functionName == "bvmul")
	{
	    if (e.num_args() != 2)
	    {
		auto toReturn = getBvecFromExpr(e.arg(0), boundVars);
		for (unsigned int i = 1; i < num; i++)
		{
		    //toReturn = toReturn * getBvecFromExpr(e.arg(i), boundVars);
		    auto argi = getBvecFromExpr(e.arg(i), boundVars);
		    toReturn = toReturn.Apply2<Bvec>(argi, [&] (auto x, auto y) { return bvec_mul(x, y); });
		    //toReturn = toReturn.bvec_coerce(e.decl().range().bv_size());
		}

		return insertIntoCaches(e, toReturn, boundVars);
	    }

	    if (e.arg(1).is_numeral())
	    {
		expr expr(*context);
		expr = e.arg(1) * e.arg(0);

		bvecExprCache.clear();
		bddExprCache.clear();
		//preciseBdds.clear();
		//sameBWPreciseBdds.clear();
		sameBWPreciseBvecs.clear();

		return getBvecFromExpr(expr, boundVars);
	    }

	    if (config.negateMul)
	    {
		if (e.arg(0).is_numeral())
		{
		    int ones = getNumeralOnes(e.arg(0));

		    if ((2U * ones) > e.arg(0).get_sort().bv_size())
		    {
			expr expr(*context);

			if (e.arg(1).is_const() || e.arg(1).is_var())
			{
			    expr = (-e.arg(0)) * -e.arg(1);
			}
			else
			{
			    expr = -(-e.arg(0) * e.arg(1));
			}

			//std::cout << e << " ~>" << expr << std::endl;

			bvecExprCache.clear();
			bddExprCache.clear();
			//preciseBdds.clear();
			//sameBWPreciseBdds.clear();
			sameBWPreciseBvecs.clear();
			return getBvecFromExpr(expr, boundVars);
		    }
		}
	    }

	    auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

	    auto result = arg0.Apply2<Bvec>(arg1, [&] (auto x, auto y) { return bvec_mul(x, y); });

	    return insertIntoCaches(e, result, boundVars);
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

	    auto [arg0, arg0OpPrecision, arg0VarPrecision] = getBvecFromExpr(e.arg(0), boundVars);
	    auto [arg1, arg1OpPrecision, arg1VarPrecision] = getBvecFromExpr(e.arg(1), boundVars);

	    Precision opPrecision = arg0OpPrecision && arg1OpPrecision;
	    Precision varPrecision = arg0VarPrecision && arg1VarPrecision;

	    int result;
	    if ((config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) &&
		operationPrecision != 0)
	    {
		if (config.limitBddSizes)
		{
		    result = Bvec::bvec_div_nodeLimit(arg0, arg1, div, rem, precisionMultiplier*operationPrecision);
		}
		else
		{
		    result = Bvec::bvec_div(arg0, arg1, div, rem, operationPrecision);
		}
	    }
	    else
	    {
		result = arg0.bvec_div(arg0, arg1, div, rem);
	    }

	    if (result == 0)
	    {
		Bvec result = rem;
		return insertIntoCaches(e, {result, opPrecision, varPrecision}, boundVars);
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

	    auto [arg0, arg0OpPrecision, arg0VarPrecision] = getBvecFromExpr(e.arg(0), boundVars);
	    auto [arg1, arg1OpPrecision, arg1VarPrecision] = getBvecFromExpr(e.arg(1), boundVars);

	    Precision opPrecision = arg0OpPrecision && arg1OpPrecision;
	    Precision varPrecision = arg0VarPrecision && arg1VarPrecision;

	    int result;
	    if ((config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) &&
		operationPrecision != 0)
	    {
		if (config.limitBddSizes)
		{
		    result = Bvec::bvec_div_nodeLimit(arg0, arg1, div, rem, precisionMultiplier*operationPrecision);
		}
		else
		{
		    result = Bvec::bvec_div(arg0, arg1, div, rem, operationPrecision);
		}

	    }
	    else
	    {
		result = arg0.bvec_div(arg0, arg1, div, rem);
	    }

	    if (result == 0)
	    {
		Bvec result = div;
		return insertIntoCaches(e, {result, opPrecision, varPrecision}, boundVars);
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
	    //preciseBdds.clear();
	    preciseBvecs.clear();
	    //sameBWPreciseBdds.clear();
	    sameBWPreciseBvecs.clear();

	    auto result = getBvecFromExpr(e, boundVars);
	    return insertIntoCaches(e, result, boundVars);
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
	    //preciseBdds.clear();
	    preciseBvecs.clear();
	    //sameBWPreciseBdds.clear();
	    sameBWPreciseBvecs.clear();

	    auto result = getBvecFromExpr(e, boundVars);
	    return insertIntoCaches(e, result, boundVars);
	}
	else if (functionName == "if")
	{
	    if (e.num_args() != 3)
	    {
		std::cout << "if -- unsupported number of arguments" << std::endl;
		std::cout << "unknown" << std::endl;
		exit(1);
	    }

	    //TODO: Tohle může být nekorektní kvůli isPositive!!!q
	    auto arg0 = approximation == OVERAPPROXIMATION ?
		getBDDFromExpr(e.arg(0), boundVars, false, true).upper :
		getBDDFromExpr(e.arg(0), boundVars, false, true).lower;
	    auto maybeArg0 = MaybeBDD(bddManager, arg0);
	    auto arg1 = getBvecFromExpr(e.arg(1), boundVars).value;
	    auto arg2 = getBvecFromExpr(e.arg(2), boundVars).value;

	    Precision opPrecision = APPROXIMATED;
	    Precision varPrecision = APPROXIMATED;

	    auto result = Bvec::bvec_ite(maybeArg0, arg1, arg2);
	    return insertIntoCaches(e, {result, opPrecision, varPrecision}, boundVars);
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

unsigned int ExprToBDDTransformer::getNumeralValue(const expr &e) const
{
    std::unique_lock<std::mutex> lk(Solver::m_z3context);
    return HexHelper::get_numeral_value(e.to_string());
}

unsigned int ExprToBDDTransformer::getNumeralOnes(const expr &e) const
{
    std::unique_lock<std::mutex> lk(Solver::m_z3context);
    return HexHelper::numeral_get_bin_zeroes(e.to_string());
}

Bvec ExprToBDDTransformer::getNumeralBvec(const z3::expr &e)
{
    z3::sort s = e.get_sort();

    std::string numeralString;
    {
	std::lock_guard<std::mutex> lg(Solver::m_z3context);
	numeralString = e.to_string();
    }

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
    approximation = NO_APPROXIMATION;
    config.approximationMethod = NONE;
    variableBitWidth = 0;

    if (expression.is_app() && expression.decl().decl_kind() == Z3_OP_TRUE)
    {
        return bddManager.bddOne();
    }
    else if (expression.is_app() && expression.decl().decl_kind() == Z3_OP_FALSE)
    {
        return bddManager.bddZero();
    }

    return loadBDDsFromExpr(expression);
}

BDD ExprToBDDTransformer::ProcessUnderapproximation(int bitWidth, unsigned int precision)
{
    approximation = UNDERAPPROXIMATION;
    variableBitWidth = bitWidth;
    operationPrecision = precision;

    return loadBDDsFromExpr(expression);
}

BDD ExprToBDDTransformer::ProcessOverapproximation(int bitWidth, unsigned int precision)
{
    approximation = OVERAPPROXIMATION;
    variableBitWidth = bitWidth;
    operationPrecision = precision;

    auto result = loadBDDsFromExpr(expression);
    return result;
}

Bvec ExprToBDDTransformer::bvec_mul(Bvec &arg0, Bvec& arg1)
{
    unsigned int bitNum = arg0.bitnum();

    Bvec result(bddManager);
    if (arg0.bitnum() > 32 || arg1.bitnum() > 32 || (!arg0.bvec_isConst() && !arg1.bvec_isConst()))
    {
	int leftConstantCount = 0;
	int rightConstantCount = 0;

	for (unsigned int i = 0; i < arg0.bitnum(); i++)
	{
	    if (!arg0[i].IsVar())
	    {
		leftConstantCount++;
	    }

	    if (!arg1[i].IsVar())
	    {
		rightConstantCount++;
	    }
	}

	bool approximate = (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH);
	Bvec result(bddManager);
	if (leftConstantCount < rightConstantCount)
	{
	    if (approximate)
	    {
		if (config.limitBddSizes)
		{
		    result = Bvec::bvec_mul_nodeLimit(arg1, arg0, precisionMultiplier*operationPrecision).bvec_coerce(bitNum);
		}
		else
		{
		    result = Bvec::bvec_mul(arg1, arg0, operationPrecision).bvec_coerce(bitNum);
		}
	    }
	    else
	    {
		result = Bvec::bvec_mul(arg1, arg0).bvec_coerce(bitNum);
	    }
	}
	else
	{
	    if (approximate)
	    {
		if (config.limitBddSizes)
		{
		    result = Bvec::bvec_mul_nodeLimit(arg0, arg1, precisionMultiplier*operationPrecision).bvec_coerce(bitNum);
		}
		else
		{
		    result = Bvec::bvec_mul(arg0, arg1, operationPrecision).bvec_coerce(bitNum);
		}
	    }
	    else
	    {
		result = Bvec::bvec_mul(arg0, arg1).bvec_coerce(bitNum);
	    }
	}

	return result;
    }

    if (arg1.bvec_isConst())
    {
	swap(arg0,arg1);
    }

    if (arg0.bvec_isConst())
    {
	unsigned int val = arg0.bvec_val();

	unsigned int largestDividingTwoPower = 0;
	for (int i = 0; i < 64; i++)
	{
	    if (val % 2 == 0)
	    {
		largestDividingTwoPower++;
		val = val >> 1;
	    }
	}

	if (largestDividingTwoPower > 0)
	{
	    result = (arg1 * val) << largestDividingTwoPower;;

	    return result;
	}

	if (val > INT_MAX)
	{
	    int leftConstantCount = 0;
	    int rightConstantCount = 0;

	    for (unsigned int i = 0; i < bitNum; i++)
	    {
		if (!arg0[i].IsVar())
		{
		    leftConstantCount++;
		}

		if (!arg1[i].IsVar())
		{
		    rightConstantCount++;
		}
	    }

	    if (leftConstantCount < rightConstantCount)
	    {
		if ((config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) &&
		    (operationPrecision != 0))
		{
		    if (config.limitBddSizes)
		    {
			result = Bvec::bvec_mul_nodeLimit(arg1, arg0, precisionMultiplier*operationPrecision).bvec_coerce(bitNum);
		    }
		    else
		    {
			result = Bvec::bvec_mul(arg1, arg0, operationPrecision).bvec_coerce(bitNum);
		    }
		}
		else
		{
		    result = Bvec::bvec_mul(arg1, arg0).bvec_coerce(bitNum);
		}

		return result;
	    }
	    else
	    {
		if ((config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) &&
		    (operationPrecision != 0))
		{
		    if (config.limitBddSizes)
		    {
			result = Bvec::bvec_mul_nodeLimit(arg0, arg1, precisionMultiplier*operationPrecision).bvec_coerce(bitNum);
		    }
		    else
		    {
			result = Bvec::bvec_mul(arg0, arg1, operationPrecision).bvec_coerce(bitNum);
		    }

		}
		else
		{
		    result = Bvec::bvec_mul(arg0, arg1).bvec_coerce(bitNum);
		}

		return result;
	    }
	}
	result = arg1 * val;

	return result;
    }

    exit(1);
}

BDD ExprToBDDTransformer::applyDontCare(BDD in)
{
    return in.LICompaction(!m_dontCare);
}

Bvec ExprToBDDTransformer::applyDontCare(Bvec in)
{
    auto oldSize = in.bddNodes();

    for (uint i = 0U; i < in.bitnum(); i++)
    {
	in[i] = in[i].LICompaction(!m_dontCare);
    }

    if (oldSize > in.bddNodes())
    {
	//std::cout << "LI don't care compaction helped";
	//in.bvec_print();
    }

    return in;
}

map<string, vector<bool>> ExprToBDDTransformer::GetModel(const BDD& modelBdd)
{
    std::map<std::string, std::vector<bool>> model;
    std::vector<BDD> modelVars;

    for (const auto [name, bw] : constSet)
    {
	auto varBvec = vars.at(name);
	for (int i = bw - 1; i >= 0; i--)
	{
	    modelVars.push_back(varBvec[i]);
	}
    }

    BDD solutionBdd = modelBdd.PickOneMinterm(modelVars);

    for (const auto [name, bw] : constSet)
    {
	vector<bool> modelBV(bw);

	auto varBvec = vars.at(name);
	for (int i = 0; i < bw; i++)
	{
	    if ((solutionBdd & varBvec[i]).IsZero())
	    {
		modelBV[bw - i - 1] = false;
	    }
	    else
	    {
		modelBV[bw - i - 1] = true;
	    }
	}

	model.insert({name, modelBV});
    }

    return model;
}

void ExprToBDDTransformer::PrintModel(const BDD& modelBdd)
{
    auto model = GetModel(modelBdd);

    std::cout << "Model: " << std::endl;
    std::cout << "---" << std::endl;

    for (auto &varModel : model)
    {
	std::cout << "  " << varModel.first << " = #b";
	for (auto bit : varModel.second)
	{
	    std::cout << bit;
	}
	std::cout << ";" << std::endl;
    }

    std::cout << "---" << std::endl;
}

Approximated<Bvec> ExprToBDDTransformer::insertIntoCaches(const z3::expr& expr, const Approximated<Bvec>& bvec, const std::vector<boundVar>& boundVars)
{
    bvecExprCache.insert({(Z3_ast)expr, {bvec, boundVars}});

    if (bvec.isPrecise() == PRECISE)
    {
	preciseBvecs.insert({(Z3_ast)expr, {bvec.value, boundVars}});
    }

    if (bvec.operationPrecision == PRECISE)
    {
	sameBWPreciseBvecs.insert({(Z3_ast)expr, {bvec, boundVars}});
    }

    return bvec;
}

BDDInterval ExprToBDDTransformer::insertIntoCaches(const z3::expr& expr, const BDDInterval& bdd, const std::vector<boundVar>& boundVars)
{
    bddExprCache.insert({(Z3_ast)expr, {bdd, boundVars}});

    // if (bdd.isPrecise() == PRECISE)
    // {
    // 	preciseBdds.insert({(Z3_ast)expr, {bdd.value, boundVars}});
    // }

    // if (bdd.operationPrecision == PRECISE)
    // {
    // 	sameBWPreciseBdds.insert({(Z3_ast)expr, {bdd, boundVars}});
    // }

    return bdd;
}
