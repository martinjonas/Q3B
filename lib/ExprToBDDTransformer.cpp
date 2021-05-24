#include "ExprToBDDTransformer.h"
#include <cmath>
#include <iostream>
#include <sstream>
#include <list>
#include <algorithm>

#include "HexHelper.h"
#include "Solver.h"

const unsigned int precisionMultiplier = 1000;

using namespace std;
using namespace z3;
using namespace std::placeholders;


ExprToBDDTransformer::ExprToBDDTransformer(z3::context &ctx, z3::expr e, Config config) : config(config), expression(e)
{
    this->context = &ctx;
    configureReorder();

    loadVars();

    setApproximationType(SIGN_EXTEND);
}

void ExprToBDDTransformer::getVars(const z3::expr &e)
{
    if (processedVarsCache.find((Z3_ast)e) != processedVarsCache.end())
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

        for (unsigned i = 0; i < num; i++)
        {
            getVars(e.arg(i));
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

            std::unique_lock<std::mutex> lk(Solver::m_z3context);
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

    int offset = 0;
    for(auto const &group : orderedGroups)
    {
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

BDD ExprToBDDTransformer::loadBDDsFromExpr(expr e, bool precise)
{
    bddExprCache.clear();
    bvecExprCache.clear();

    cacheHits = 0;

    if (lastBW != variableBitWidth)
    {
        sameBWPreciseBdds.clear();
        sameBWPreciseBvecs.clear();
        lastBW = variableBitWidth;
    }

    this->expression = e;
    variableApproximationHappened = false;
    auto result = getBDDFromExpr(e, {}, true, precise);

    operationApproximationHappened = !result.IsPrecise();

    bddExprCache.clear();
    bvecExprCache.clear();

    return result;
}



BDD ExprToBDDTransformer::getConjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars, bool onlyExistentials, bool precise)
{
    return getConnectiveBdd(arguments, boundVars, onlyExistentials, precise,
                            [](auto& a, auto& b) { return a * b; },
                            [](const auto a) { return a.IsZero(); },
                            bddManager.bddOne());
}

BDD ExprToBDDTransformer::getDisjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars, bool onlyExistentials, bool precise)
{
    return getConnectiveBdd(arguments, boundVars, onlyExistentials, precise,
                            [](auto& a, auto& b) { return a + b; },
                            [](const auto a) { return a.IsOne(); },
                            bddManager.bddZero());
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
        if (cachedBoundVars[cachedBoundVars.size() - i - 1] != boundVars[boundVars.size() - i - 1])
        {
            return false;
        }
    }

    return true;
}

BDD ExprToBDDTransformer::getBDDFromExpr(const expr &e, const vector<boundVar>& boundVars, bool onlyExistentials, bool precise)
{
    if (Solver::resultComputed) return bddManager.bddZero();
    assert(e.is_bool());

    auto caches = {bddExprCache, preciseBdds, sameBWPreciseBdds};
    for (const auto& cache : caches)
    {
        auto item = cache.find((Z3_ast)e);
        if (item != cache.end())
        {
            if (correctBoundVars(boundVars, (item->second).second))
            {
                return (item->second).first;
            }
        }
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];
        return vars.at(bVar.first)[0];
    }
    else if (e.is_const())
    {
        if (e.is_app() && e.decl().decl_kind() == Z3_OP_TRUE)
        {
            return bddManager.bddOne();
        }
        else if (e.is_app() && e.decl().decl_kind() == Z3_OP_FALSE)
        {
            return bddManager.bddZero();
        }

        Solver::m_z3context.lock();
        std::string exprString = e.to_string();
        Solver::m_z3context.unlock();

        return insertIntoCaches(e, (vars.at(exprString)[0]), boundVars);
    }
    else if (e.is_app())
    {
        func_decl f = e.decl();
        unsigned num = e.num_args();

        auto decl_kind = f.decl_kind();

        if (decl_kind == Z3_OP_EQ)
        {
            checkNumberOfArguments<2>(e);

            auto sort = e.arg(0).get_sort();
            BDD result;

            assert(sort.is_bv() || sort.is_bool());
            if (sort.is_bv())
            {
                result = Bvec::bvec_equ(getBvecFromExpr(e.arg(0), boundVars, precise).value,
                                        getBvecFromExpr(e.arg(1), boundVars, precise).value);
            }
            else if (sort.is_bool())
            {
                result = getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, precise).Xnor(
                        getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, precise));
            }

            return insertIntoCaches(e, result, boundVars);
        }
        else if (decl_kind == Z3_OP_NOT)
        {
            return !getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, precise);
        }
        else if (decl_kind == Z3_OP_AND)
        {
            vector<expr> arguments;

            for (unsigned int i = 0; i < num; i++)
            {
                arguments.push_back(e.arg(i));
            }

            auto result = getConjunctionBdd(arguments, boundVars, onlyExistentials, precise);
            return insertIntoCaches(e, result, boundVars);
        }
        else if (decl_kind == Z3_OP_OR)
        {
            vector<expr> arguments;
            for (unsigned int i = 0; i < num; i++)
            {
                arguments.push_back(e.arg(i));
            }

            auto result = getDisjunctionBdd(arguments, boundVars, onlyExistentials, precise);
            return insertIntoCaches(e, result, boundVars);
        }
        else if (decl_kind == Z3_OP_IMPLIES)
        {
            checkNumberOfArguments<2>(e);

            auto result = !getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, precise) +
                          getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, precise);
            return insertIntoCaches(e, result, boundVars);
        }
        else if (decl_kind == Z3_OP_ULEQ)
        {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBvecFromExpr(e.arg(0), boundVars, precise).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars, precise).value;

            if (Solver::resultComputed) return bddManager.bddZero();
            return insertIntoCaches(e, Bvec::bvec_lte(arg0, arg1, precise), boundVars);
        }
        else if (decl_kind == Z3_OP_ULT)
        {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBvecFromExpr(e.arg(0), boundVars, precise).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars, precise).value;

            if (Solver::resultComputed) return bddManager.bddZero();
            return insertIntoCaches(e, Bvec::bvec_lth(arg0, arg1, precise), boundVars);
        }
        else if (decl_kind == Z3_OP_UGEQ)
        {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBvecFromExpr(e.arg(0), boundVars, precise).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars, precise).value;

            if (Solver::resultComputed) return bddManager.bddZero();
            return insertIntoCaches(e, Bvec::bvec_lte(arg1, arg0, precise), boundVars);
        }
        else if (decl_kind == Z3_OP_UGT)
        {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBvecFromExpr(e.arg(0), boundVars, precise).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars, precise).value;

            if (Solver::resultComputed) return bddManager.bddZero();
            return insertIntoCaches(e, Bvec::bvec_lth(arg1, arg0, precise), boundVars);
        }
        else if (decl_kind == Z3_OP_SLEQ)
        {
            checkNumberOfArguments<2>(e);

            BDD result;
            auto arg0 = getBvecFromExpr(e.arg(0), boundVars, precise).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars, precise).value;
            if (Solver::resultComputed) return bddManager.bddZero();

            result = Bvec::bvec_slte(arg0, arg1, precise);

            return insertIntoCaches(e, result, boundVars);
        }
        else if (decl_kind == Z3_OP_SLT)
        {
            checkNumberOfArguments<2>(e);

            BDD result;
            auto arg0 = getBvecFromExpr(e.arg(0), boundVars, precise).value;
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars, precise).value;
            if (Solver::resultComputed) return bddManager.bddZero();

            result = Bvec::bvec_slth(arg0, arg1, precise);

            return insertIntoCaches(e, result, boundVars);
        }
        else if (decl_kind == Z3_OP_IFF)
        {
            checkNumberOfArguments<2>(e);

            auto arg0 = getBDDFromExpr(e.arg(0), boundVars, false, precise);
            auto arg1 = getBDDFromExpr(e.arg(1), boundVars, false, precise);

            if (Solver::resultComputed) return bddManager.bddZero();
            auto result = arg0.Xnor(arg1);
            return insertIntoCaches(e, result, boundVars);
        }
        else if (decl_kind == Z3_OP_ITE)
        {
            checkNumberOfArguments<3>(e);

            auto arg0 = getBDDFromExpr(e.arg(0), boundVars, onlyExistentials, precise);
            auto arg1 = getBDDFromExpr(e.arg(1), boundVars, onlyExistentials, precise);
            auto arg2 = getBDDFromExpr(e.arg(2), boundVars, onlyExistentials, precise);

            if (Solver::resultComputed) return bddManager.bddZero();
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

            std::unique_lock<std::mutex> lk(Solver::m_z3context);
            newBoundVars.push_back(std::pair<string, BoundType>(current_symbol.str(), bt));
        }

        BDD bodyBdd;
        if (onlyExistentials)
        {
            if (Z3_is_quantifier_forall(*context, ast))
            {
                //only existentials so far, but this one is universal
                bodyBdd = getBDDFromExpr(e.body(), newBoundVars, false, precise);
            }
            else
            {
                //only existentials so far and this one is also existential
                auto oldBDDCache = bddExprCache;
                auto oldBvecCache = bvecExprCache;
                auto result = getBDDFromExpr(e.body(), newBoundVars, true, precise);
                //we need to revert the state of the cache, because of
                //the bound variables with the same names
                bddExprCache = oldBDDCache;
                bvecExprCache = oldBvecCache;
                return result;
            }
        }
        else
        {
            bodyBdd = getBDDFromExpr(e.body(), newBoundVars, false, precise);
        }

        //prune caches that will never be used again
        for(auto it = bddExprCache.begin(); it != bddExprCache.end(); )
        {
            if ((it->second).second == newBoundVars)
            {
                it = bddExprCache.erase(it);
            }
            else
            {
                it++;
            }
        }

        for(auto it = bvecExprCache.begin(); it != bvecExprCache.end(); )
        {
            if ((it->second).second == newBoundVars)
            {
                it = bvecExprCache.erase(it);
            }
            else
            {
                it++;
            }
        }

        for (int i = boundVariables - 1; i >= 0; i--)
        {
            if (Solver::resultComputed) return bddManager.bddZero();
            Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
            symbol current_symbol(*context, z3_symbol);

            Solver::m_z3context.lock();
            auto varSet = varSets.at(current_symbol.str());
            Solver::m_z3context.unlock();
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
    if (newBitWidth == 0)
    {
        return {var, PRECISE, PRECISE};
    }

    variableApproximationHappened = true;

    bool flip = newBitWidth < 0;
    newBitWidth = abs(newBitWidth);

    newBitWidth = min(newBitWidth, (int)var.bitnum());
    int leftBits = newBitWidth / 2;
    int rightBits = newBitWidth - leftBits;

    if (flip)
    {
        swap(leftBits, rightBits);
    }

    if (at == ZERO_EXTEND)
    {
        for (int i = var.bitnum() - leftBits - 1; i >= rightBits; i--)
        {
            var.set(i, bddManager.bddZero());
        }
    }
    else if (at == SIGN_EXTEND && rightBits != 0)
    {
        for (unsigned int i = rightBits; i < var.bitnum() - leftBits; i++)
        {
            var.set(i, var[i - 1]);
        }
    }
    else if (at == SIGN_EXTEND && rightBits == 0)
    {
        for (int i = var.bitnum() - leftBits - 1; i >= 0; i--)
        {
            var.set(i, var[i + 1]);
        }
    }

    return {var, PRECISE, APPROXIMATED};
}

Approximated<Bvec> ExprToBDDTransformer::getBvecFromExpr(const expr &e, const vector<boundVar>& boundVars, bool precise)
{
    assert(e.is_bv());
    if (Solver::resultComputed) return {Bvec::bvec_con(bddManager, e.get_sort().bv_size(), 0), APPROXIMATED};

    auto caches = {bvecExprCache, preciseBvecs, sameBWPreciseBvecs};
    for (const auto& cache : caches)
    {
        auto item = cache.find((Z3_ast)e);
        if (item != cache.end() && correctBoundVars(boundVars, (item->second).second))
        {
            return (item->second).first;
        }
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];

        if ((config.approximationMethod == VARIABLES || config.approximationMethod == BOTH)  &&
            ((bVar.second == EXISTENTIAL && approximation == UNDERAPPROXIMATION) ||
             (bVar.second == UNIVERSAL && approximation == OVERAPPROXIMATION)))
        {
            return getApproximatedVariable(bVar.first, variableBitWidth, approximationType);
        }


        return insertIntoCaches(e, {vars.at(bVar.first), PRECISE}, boundVars);
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

        std::unique_lock<std::mutex> lk(Solver::m_z3context);
        return insertIntoCaches(e, {vars.at(e.to_string()), PRECISE}, boundVars);
    }
    else if (e.is_app())
    {
        func_decl f = e.decl();
        unsigned num = e.num_args();

        auto decl_kind = f.decl_kind();

        if (decl_kind == Z3_OP_BADD)
        {
            if ((config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) &&
                operationPrecision != 0)
            {
                return bvec_assocOp(e, std::bind(Bvec::bvec_add_nodeLimit, _1, _2, precisionMultiplier*operationPrecision), boundVars, precise);
            }

            return bvec_assocOp(e, [&] (auto x, auto y) { return x + y; }, boundVars, precise);
        }
        else if (decl_kind == Z3_OP_BSUB)
        {
            checkNumberOfArguments<2>(e);
            return bvec_binOp(e, [] (auto x, auto y) { return x - y; }, boundVars, precise);
        }
        else if (decl_kind == Z3_OP_BSHL)
        {
            if (e.arg(1).is_numeral())
            {
                return bvec_unOp(e, [&] (auto x) { return x << getNumeralValue(e.arg(1)); }, boundVars, precise);
            }
            else
            {
                return bvec_binOp(e, [] (auto x, auto y) { return x << y; }, boundVars, precise);
            }
        }
        else if (decl_kind == Z3_OP_BLSHR)
        {
            if (e.arg(1).is_numeral())
            {
                return bvec_unOp(e, [&] (auto x) { return x >> getNumeralValue(e.arg(1)); }, boundVars, precise);
            }
            else
            {
                return bvec_binOp(e, [] (auto x, auto y) { return x >> y; }, boundVars, precise);
            }
        }
        else if (decl_kind == Z3_OP_BASHR)
        {
            auto bitwidth = e.get_sort().bv_size();
            if (e.arg(1).is_numeral())
            {
                return bvec_unOp(e, [&] (auto x) { return x.bvec_shrfixed(getNumeralValue(e.arg(1)), x[bitwidth - 1]); }, boundVars, precise);
            }
            else
            {
                return bvec_binOp(e, [&] (auto x, auto y) { return Bvec::bvec_shr(x, y, x[bitwidth - 1], precise); }, boundVars, precise);
            }
        }
        else if (decl_kind == Z3_OP_CONCAT)
        {
            int newSize = f.range().bv_size();
            int offset = 0;

            auto currentBvec = Bvec::bvec_false(bddManager, newSize);
            Precision opPrecision = PRECISE;
            Precision varPrecision = PRECISE;

            assert(num > 0);
            for (int i = num-1; i >= 0; i--)
            {
                auto [arg, argOpPrecision, argVarPrecision] = getBvecFromExpr(e.arg(i), boundVars, precise);
                currentBvec = Bvec::bvec_map2(currentBvec,
                                              arg.bvec_coerce(newSize) << offset,
                                              [&](const BDD &a, const BDD &b) { return a ^ b; });
                opPrecision = opPrecision && argOpPrecision;
                varPrecision = varPrecision && argVarPrecision;
                offset += f.domain(i).bv_size();
            }

            return insertIntoCaches(e, {currentBvec, opPrecision, varPrecision}, boundVars);
        }
        else if (decl_kind == Z3_OP_EXTRACT)
        {
            Z3_func_decl z3decl = (Z3_func_decl)e.decl();

            int bitTo = Z3_get_decl_int_parameter(*context, z3decl, 0);
            int bitFrom = Z3_get_decl_int_parameter(*context, z3decl, 1);

            int extractBits = bitTo - bitFrom + 1;

            return bvec_unOp(e,
                             [&] (auto x) { return x
                                     .bvec_shrfixed(bitFrom, bddManager.bddZero())
                                     .bvec_coerce(extractBits); },
                             boundVars,
                             precise);
        }
        else if (decl_kind == Z3_OP_BNOT)
        {
            return bvec_unOp(e, std::bind(Bvec::bvec_map1, _1, [&](const BDD &a) { return !a; }), boundVars, precise);
        }
        else if (decl_kind == Z3_OP_BNEG)
        {
            return bvec_unOp(e, [&] (auto x) { return Bvec::arithmetic_neg(x); }, boundVars, precise);
        }
        else if (decl_kind == Z3_OP_BOR)
        {
            return bvec_assocOp(e, [&](const Bvec &a, const Bvec &b) { return a | b; }, boundVars, precise);
        }
        else if (decl_kind == Z3_OP_BAND)
        {
            return bvec_assocOp(e, [&](const Bvec &a, const Bvec &b) { return a & b; }, boundVars, precise);
        }
        else if (decl_kind == Z3_OP_BXOR)
        {
            return bvec_assocOp(e, [&](const Bvec &a, const Bvec &b) { return a ^ b; }, boundVars, precise);
        }
        else if (decl_kind == Z3_OP_BMUL)
        {
            return bvec_assocOp(e, [&](auto x, auto y){ return bvec_mul(x, y); }, boundVars, precise);
        }
        else if (decl_kind == Z3_OP_BUREM || decl_kind == Z3_OP_BUREM_I || decl_kind == Z3_OP_BUDIV || decl_kind == Z3_OP_BUDIV_I)
        {
            checkNumberOfArguments<2>(e);

            Bvec div = Bvec::bvec_false(bddManager, e.decl().range().bv_size());
            Bvec rem = Bvec::bvec_false(bddManager, e.decl().range().bv_size());

            auto [arg0, arg0OpPrecision, arg0VarPrecision] = getBvecFromExpr(e.arg(0), boundVars, precise);
            auto [arg1, arg1OpPrecision, arg1VarPrecision] = getBvecFromExpr(e.arg(1), boundVars, precise);

            Precision opPrecision = arg0OpPrecision && arg1OpPrecision;
            Precision varPrecision = arg0VarPrecision && arg1VarPrecision;

            int result = 0;
            if (e.arg(1).is_numeral() && e.get_sort().bv_size() <= 32)
            {
                result = arg0.bvec_divfixed(getNumeralValue(e.arg(1)), div, rem, precise);
            }
            else if ((config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) &&
                     operationPrecision != 0)
            {
                result = Bvec::bvec_div_nodeLimit(arg0, arg1, div, rem, precisionMultiplier*operationPrecision);
            }
            else
            {
                result = arg0.bvec_div(arg0, arg1, div, rem);
            }

            if (result == 0)
            {
                return insertIntoCaches(e, {decl_kind == Z3_OP_BUDIV || decl_kind == Z3_OP_BUDIV_I ? div : rem, opPrecision, varPrecision}, boundVars);
            }
            else
            {
                cout << "ERROR: division error" << endl;
                cout << "unknown";
                exit(0);
            }
        }
        else if (decl_kind == Z3_OP_BSDIV || decl_kind == Z3_OP_BSDIV_I)
        {
            checkNumberOfArguments<2>(e);

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

            clearCaches();

            auto result = getBvecFromExpr(e, boundVars, precise);
            return insertIntoCaches(e, result, boundVars);
        }
        else if (decl_kind == Z3_OP_BSREM || decl_kind == Z3_OP_BSREM_I)
        {
            checkNumberOfArguments<2>(e);

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
            clearCaches();

            auto result = getBvecFromExpr(e, boundVars, precise);
            return insertIntoCaches(e, result, boundVars);
        }
        else if (decl_kind == Z3_OP_ITE)
        {
            checkNumberOfArguments<3>(e);

            auto arg0 = getBDDFromExpr(e.arg(0), boundVars, false, precise);
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars, precise).value;
            auto arg2 = getBvecFromExpr(e.arg(2), boundVars, precise).value;

            auto result = Bvec::bvec_ite(arg0, arg1, arg2);
            return insertIntoCaches(e, {result, APPROXIMATED, APPROXIMATED}, boundVars);
        }
        else
        {
            cout << "ERROR: not supported function " << e << endl;
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

    return loadBDDsFromExpr(expression, true);
}

BDD ExprToBDDTransformer::ProcessUnderapproximation(int bitWidth, unsigned int precision)
{
    approximation = UNDERAPPROXIMATION;
    variableBitWidth = bitWidth;
    operationPrecision = precision;

    return loadBDDsFromExpr(expression, false);
}

BDD ExprToBDDTransformer::ProcessOverapproximation(int bitWidth, unsigned int precision)
{
    approximation = OVERAPPROXIMATION;
    variableBitWidth = bitWidth;
    operationPrecision = precision;

    return loadBDDsFromExpr(expression, false);
}

Bvec ExprToBDDTransformer::bvec_mul(Bvec &arg0, Bvec& arg1)
{
    unsigned int bitNum = arg0.bitnum();

    if (isMinusOne(arg0))
    {
        Bvec::arithmetic_neg(arg1);
    }
    else if (isMinusOne(arg1))
    {
        Bvec::arithmetic_neg(arg0);
    }

    Bvec result(bddManager);
    if (arg0.bitnum() <= 32 && arg1.bitnum() <= 32)
    {
        if (arg1.bvec_isPreciseConst())
        {
            swap(arg0,arg1);
        }

        if (arg0.bvec_isPreciseConst())
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

            if (val <= INT_MAX)
            {
                return arg1 * val;
            }
        }
    }

    int leftConstantCount = 0;
    int rightConstantCount = 0;

    for (unsigned int i = 0; i < arg0.bitnum(); i++)
    {
        if (arg0[i].IsZero() || arg0[i].IsOne())
        {
            leftConstantCount++;
        }

        if (arg1[i].IsZero() || arg1[i].IsOne())
        {
            rightConstantCount++;
        }
    }

    if (leftConstantCount < rightConstantCount)
    {
        swap(arg0, arg1);
    }

    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)
    {
        return Bvec::bvec_mul_nodeLimit(arg0, arg1, precisionMultiplier*operationPrecision).bvec_coerce(bitNum);
    }

    return Bvec::bvec_mul(arg0, arg1).bvec_coerce(bitNum);
}

Approximated<Bvec> ExprToBDDTransformer::bvec_assocOp(const z3::expr& e, const std::function<Bvec(Bvec, Bvec)>& op, const std::vector<boundVar>& boundVars, bool precise)
{
    if (Solver::resultComputed) return {Bvec::bvec_con(bddManager, e.get_sort().bv_size(), 0), APPROXIMATED, APPROXIMATED};
    unsigned num = e.num_args();
    auto toReturn = getBvecFromExpr(e.arg(0), boundVars, precise);
    for (unsigned int i = 1; i < num; i++)
    {
        toReturn = toReturn.Apply2<Bvec>(getBvecFromExpr(e.arg(i), boundVars, precise), op);
    }

    return insertIntoCaches(e, toReturn, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::bvec_binOp(const z3::expr& e, const std::function<Bvec(Bvec, Bvec)>& op, const std::vector<boundVar>& boundVars, bool precise)
{
    if (Solver::resultComputed) return {Bvec::bvec_con(bddManager, e.get_sort().bv_size(), 0), APPROXIMATED, APPROXIMATED};
    auto result = getBvecFromExpr(e.arg(0), boundVars, precise).Apply2<Bvec>(
            getBvecFromExpr(e.arg(1), boundVars, precise),
            op);

    return insertIntoCaches(e, result, boundVars);
}

Approximated<Bvec> ExprToBDDTransformer::bvec_unOp(const z3::expr& e, const std::function<Bvec(Bvec)>& op, const std::vector<boundVar>& boundVars, bool precise)
{
    if (Solver::resultComputed) return {Bvec::bvec_con(bddManager, e.get_sort().bv_size(), 0), APPROXIMATED, APPROXIMATED};
    auto result = getBvecFromExpr(e.arg(0), boundVars, precise).Apply<Bvec>(op);

    return insertIntoCaches(e, result, boundVars);
}

map<string, vector<bool>> ExprToBDDTransformer::GetModel(BDD modelBdd, BDDType type)
{
    std::map<std::string, std::vector<bool>> model;
    std::vector<BDD> modelVars;

    for (const auto& [name, bw] : constSet)
    {
        auto varBvec = vars.at(name);
        for (int i = bw - 1; i >= 0; i--)
        {
            if (varBvec[i].IsVar())
            {
                modelVars.push_back(varBvec[i]);
            }
            else assert(false); // should never happen
        }
    }

    /* Does not contain [?] target. */
    switch (type) {
        case PRECISE_BDD:
            modelBdd = modelBdd.PickOneMinterm(modelVars);
            break;
        case OVER_APPROX_BDD:
            modelBdd = modelBdd.ForgetOnes().PickOneMintermOver(modelVars);
            break;
        case UNDER_APPROX_BDD:
            modelBdd = modelBdd.ForgetZeros().PickOneMintermUnder(modelVars);
            break;
    }

    for (const auto& [name, bw] : constSet)
    {
        vector<bool> modelBV(bw);

        auto varBvec = vars.at(name);
        for (int i = 0; i < bw; i++)
        {
            if ((modelBdd & !varBvec[i]).IsZero())
            {
                modelBV[bw - i - 1] = true;
                modelBdd &= varBvec[i];
            }
            else
            {
                modelBV[bw - i - 1] = false;
                modelBdd &= !varBvec[i];
            }
        }

        model.insert({name, modelBV});
    }

    return model;
}

void ExprToBDDTransformer::PrintModel(const map<string, vector<bool>>& model)
{
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

void ExprToBDDTransformer::PrintNecessaryVarValues(BDD bdd, const std::string& varName)
{
    if (!config.propagateNecessaryBits || variableBitWidth > 2)
    {
        return;
    }

    bdd = bdd.FindEssential();

    auto& bvec = vars.at(varName);

    bool newVal = false;
    for (unsigned i = 0; i < bvec.bitnum(); i++)
    {
        if ((bdd & !bvec[i]).IsZero())
        {
            bvec[i] = bddManager.bddOne();
            newVal = true;
        }
        else if ((bdd & bvec[i]).IsZero())
        {
            bvec[i] = bddManager.bddZero();
            newVal = true;
        }
        else if (i != bvec.bitnum() - 1 && (bdd & (bvec[bvec.bitnum() - 1] ^ bvec[i])).IsZero())
        {
            bvec[i] = bvec[bvec.bitnum() - 1];
            newVal = true;
        }
    }

    if (newVal)
    {
        bddExprCache.clear();
        bvecExprCache.clear();
    }
}

void ExprToBDDTransformer::PrintNecessaryValues(BDD bdd)
{
    for (const auto& c : constSet)
    {
        PrintNecessaryVarValues(bdd, c.first);
    }
}


Approximated<Bvec> ExprToBDDTransformer::insertIntoCaches(const z3::expr& expr, const Approximated<Bvec>& bvec, const std::vector<boundVar>& boundVars)
{
    if (Solver::resultComputed) return {Bvec::bvec_con(bddManager, expr.get_sort().bv_size(), 0), APPROXIMATED, APPROXIMATED};
    bvecExprCache.insert({(Z3_ast)expr, {bvec, boundVars}});

    if (bvec.value.isPrecise())
    {
        sameBWPreciseBvecs.insert({(Z3_ast)expr, {bvec, boundVars}});
    }

    return bvec;
}

BDD ExprToBDDTransformer::insertIntoCaches(const z3::expr& expr, const BDD& bdd, const std::vector<boundVar>& boundVars)
{
    if (Solver::resultComputed) return bddManager.bddZero();
    bddExprCache.insert({(Z3_ast)expr, {bdd, boundVars}});

    if (bdd.IsPrecise())
    {
        sameBWPreciseBdds.insert({(Z3_ast) expr, {bdd, boundVars}});
    }

    return bdd;
}

bool ExprToBDDTransformer::isMinusOne(const Bvec& bvec)
{
    return std::all_of(bvec.m_bitvec.begin(), bvec.m_bitvec.begin(), [] (auto& bit) { return bit.IsOne(); });
}

void ExprToBDDTransformer::clearCaches()
{
    bddExprCache.clear();
    bvecExprCache.clear();
    preciseBdds.clear();
    preciseBvecs.clear();
    sameBWPreciseBdds.clear();
    sameBWPreciseBvecs.clear();
}

bool ExprToBDDTransformer::isInterrupted()
{
    return Solver::resultComputed;
}
