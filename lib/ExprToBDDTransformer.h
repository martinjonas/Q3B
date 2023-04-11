#ifndef ExprToBDDTransformer_h
#define ExprToBDDTransformer_h

#include <string>
#include <set>
#include <vector>
#include <map>
#include <functional>
#include <unordered_map>
#include "cudd.h"
#include <cuddObj.hh>
#include "cudd/bvec_cudd.h"
#include <z3++.h>
#include "VariableOrderer.h"
#include "Approximated.h"
#include "Config.h"

typedef std::pair<std::string, int> var;

enum BoundType { EXISTENTIAL, UNIVERSAL };
enum ApproximationType { ZERO_EXTEND, SIGN_EXTEND };
enum Approximation { UNDERAPPROXIMATION, OVERAPPROXIMATION, NO_APPROXIMATION};

/* PRECISE_BDD      : [0], [1]
 * OVER_APPROX_BDD  : [0], [?]   ([1] -> [?])
 * UNDER_APPROX_BDD : [?], [1]   ([0] -> [?]) */
enum BDDType { PRECISE_BDD, OVER_APPROX_BDD, UNDER_APPROX_BDD };

typedef std::pair<std::string, BoundType> boundVar;

using namespace cudd;

class ExprToBDDTransformer
{
  private:
    Cudd bddManager;

    std::map<std::string, Bvec> vars;
    std::map<std::string, BDD> varSets;
    std::map<std::string, std::vector<int>> varIndices;

    std::set<var> constSet;
    std::set<var> boundVarSet;

    std::map<const Z3_ast, std::pair<BDD, std::vector<boundVar>>> bddExprCache;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> bvecExprCache;

    std::map<const Z3_ast, std::pair<BDD, std::vector<boundVar>>> preciseBdds;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> preciseBvecs;

    int lastBW = 0;
    std::map<const Z3_ast, std::pair<BDD, std::vector<boundVar>>> sameBWPreciseBdds;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> sameBWPreciseBvecs;

    Approximated<Bvec> insertIntoCaches(const z3::expr&, const Approximated<Bvec>&, const std::vector<boundVar>&);
    BDD insertIntoCaches(const z3::expr&, const BDD&, const std::vector<boundVar>&);

    std::set<Z3_ast> processedVarsCache;

    z3::context* context;

    void getVars(const z3::expr &e);
    void loadVars();

    BDD loadBDDsFromExpr(z3::expr, bool precise);
    bool correctBoundVars(const std::vector<boundVar>&, const std::vector<boundVar>&) const;
    BDD getBDDFromExpr(const z3::expr&, const std::vector<boundVar>&, bool onlyExistentials, bool precise);
    Approximated<Bvec> getApproximatedVariable(const std::string&, int, const ApproximationType&);
    Approximated<Bvec> getBvecFromExpr(const z3::expr&, const std::vector<boundVar>&, bool precise);

    unsigned int getNumeralValue(const z3::expr&) const;
    Bvec getNumeralBvec(const z3::expr&);
    bool isMinusOne(const Bvec&);

    template < typename Top,  typename TisDefinite, typename TdefaultResult >
    BDD getConnectiveBdd(const std::vector<z3::expr>& arguments, const std::vector<boundVar>& boundVars, bool onlyExistentials,
                         bool precise, Top&& op, TisDefinite&& isDefinite, TdefaultResult&& defaultResult)
    {
        std::vector<BDD> results;

        for (unsigned int i = 0; i < arguments.size(); i++)
        {
            if (isInterrupted()) { return defaultResult; }
            auto argBdd = getBDDFromExpr(arguments[i], boundVars, onlyExistentials, precise);

            if (isDefinite(argBdd)) { return argBdd; }
            else { results.push_back(argBdd); }
        }

        if (results.size() == 0) { return defaultResult; }
        else
        {
            std::sort(results.begin(), results.end(),
                      [&](const auto a, const auto b) -> bool
                          {
                              return bddManager.nodeCount(std::vector<BDD>{a}) < bddManager.nodeCount(std::vector<BDD>{b});
                          });

            auto toReturn = results.at(0);

            for (unsigned int i = 1; i < results.size(); i++)
            {
                if (isInterrupted()) { return defaultResult; }
                if (isDefinite(toReturn)) { return toReturn; }

                toReturn = op(toReturn, results.at(i));
            }

            return toReturn;
        }
    }

    BDD getConjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bool, bool);
    BDD getDisjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bool, bool);

    Approximation approximation;
    int variableBitWidth;

    unsigned int operationPrecision;

    ApproximationType approximationType;

    bool variableApproximationHappened = false;
    bool operationApproximationHappened = false;

    int cacheHits = 0;

    Bvec bvec_mul(Bvec&, Bvec&);
    Approximated<Bvec> bvec_assocOp(const z3::expr&, const std::function<Bvec(Bvec, Bvec)>&, const std::vector<boundVar>&, bool precise);
    Approximated<Bvec> bvec_binOp(const z3::expr&, const std::function<Bvec(Bvec, Bvec)>&, const std::vector<boundVar>&, bool precise);
    Approximated<Bvec> bvec_unOp(const z3::expr&, const std::function<Bvec(Bvec)>&, const std::vector<boundVar>&, bool precise);

    Config config;

    void clearCaches();

    template< int n >
    void checkNumberOfArguments(const z3::expr& e)
    {
        if (e.num_args() != n)
        {
            std::cout << e << " -- unsupported number of arguments" << std::endl;
            std::cout << "unknown" << std::endl;
            exit(1);
        }
    }

    bool isInterrupted();

  public:
    ExprToBDDTransformer(z3::context& context, z3::expr e, Config config);

    z3::expr expression;
    BDD Proccess();

    BDD ProcessUnderapproximation(int, unsigned int);
    BDD ProcessOverapproximation(int, unsigned int);

    void setApproximationType(ApproximationType at)
    {
        approximationType = at;
    }

    bool IsPreciseResult()
    {
        return !variableApproximationHappened && !operationApproximationHappened;
    }

    bool VariableApproximationHappened()
    {
        return variableApproximationHappened;
    }

    bool OperationApproximationHappened()
    {
        return operationApproximationHappened;
    }

    void configureReorder()
    {
        if (config.reorderType != NO_REORDER)
        {
          switch (config.reorderType)
          {
              case WIN2:
                  bddManager.AutodynEnable(CUDD_REORDER_WINDOW2);
                  break;
              case WIN2_ITE:
                  bddManager.AutodynEnable(CUDD_REORDER_WINDOW2_CONV);
                  break;
              case WIN3:
                  bddManager.AutodynEnable(CUDD_REORDER_WINDOW3);
                  break;
              case WIN3_ITE:
                  bddManager.AutodynEnable(CUDD_REORDER_WINDOW3_CONV);
                  break;
              case SIFT:
                  bddManager.SetMaxGrowth(1.05);
                  bddManager.SetSiftMaxVar(1);
                  bddManager.AutodynEnable(CUDD_REORDER_SYMM_SIFT);
                  break;
              case SIFT_ITE:
                  bddManager.SetMaxGrowth(1.05);
                  bddManager.SetSiftMaxVar(1);
                  bddManager.AutodynEnable(CUDD_REORDER_SYMM_SIFT_CONV);
                  break;
              default:
                  break;
          }
        }
    }

    void PrintModel(const std::map<std::string, std::vector<bool>>&);
    std::map<std::string, std::vector<bool>> GetModel(BDD, BDDType);

    void PrintNecessaryValues(BDD);
    void PrintNecessaryVarValues(BDD, const std::string&);
};

#endif
