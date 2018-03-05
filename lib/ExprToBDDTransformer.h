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
#include "../BDD/cudd/bvec_cudd.h"
#include <z3++.h>
#include "VariableOrderer.h"
#include "Approximated.h"
#include "Config.h"

typedef std::pair<std::string, int> var;

enum BoundType { EXISTENTIAL, UNIVERSAL };
enum ApproximationType { ZERO_EXTEND, SIGN_EXTEND };
enum Approximation { UNDERAPPROXIMATION, OVERAPPROXIMATION, NO_APPROXIMATION };

typedef std::pair<std::string, BoundType> boundVar;

using namespace cudd;

class ExprToBDDTransformer
{
  private:
    std::map<std::string, Bvec> vars;
    std::map<std::string, BDD> varSets;
    std::map<std::string, std::vector<int>> varIndices;

    std::set<var> constSet;
    std::set<var> boundVarSet;

    std::map<const Z3_ast, std::pair<Approximated<BDD>, std::vector<boundVar>>> bddExprCache;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> bvecExprCache;

    std::map<const Z3_ast, std::pair<BDD, std::vector<boundVar>>> preciseBdds;
    std::map<const Z3_ast, std::pair<Bvec, std::vector<boundVar>>> preciseBvecs;

    int lastBW = 0;
    std::map<const Z3_ast, std::pair<Approximated<BDD>, std::vector<boundVar>>> sameBWPreciseBdds;
    std::map<const Z3_ast, std::pair<Approximated<Bvec>, std::vector<boundVar>>> sameBWPreciseBvecs;

    Approximated<Bvec> insertIntoCaches(const z3::expr&, const Approximated<Bvec>&, const std::vector<boundVar>&);
    Approximated<BDD> insertIntoCaches(const z3::expr&, const Approximated<BDD>&, const std::vector<boundVar>&);

    std::set<Z3_ast> processedVarsCache;

    z3::context* context;

    void getVars(const z3::expr &e);
    void loadVars();

    Approximated<BDD> loadBDDsFromExpr(z3::expr);
    bool correctBoundVars(const std::vector<boundVar>&, const std::vector<boundVar>&) const;
    Approximated<BDD> getBDDFromExpr(const z3::expr&, const std::vector<boundVar>&, bool onlyExistentials, bool isPositive);
    Approximated<Bvec> getApproximatedVariable(const std::string&, int, const ApproximationType&);
    Approximated<Bvec> getBvecFromExpr(const z3::expr&, const std::vector<boundVar>&);

    unsigned int getNumeralValue(const z3::expr&) const;
    unsigned int getNumeralOnes(const z3::expr&) const;
    Bvec getNumeralBvec(const z3::expr&);

    Approximated<BDD> getConjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bool, bool);
    Approximated<BDD> getDisjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bool, bool);

    int approximation;
    int variableBitWidth;

    unsigned int operationPrecision;

    ApproximationType approximationType;

    bool variableApproximationHappened = false;
    bool operationApproximationHappened = false;

    int cacheHits = 0;

    Cudd bddManager;

    Bvec bvneg(Bvec bv, int bitSize);
    Bvec bvec_mul(Bvec&, Bvec&);

    BDD m_dontCare;
    BDD applyDontCare(BDD);
    Bvec applyDontCare(Bvec);

    Config config;

  public:
    ExprToBDDTransformer(z3::context& context, z3::expr e, Config config);

    ~ExprToBDDTransformer()
    {
	vars.clear();
	varSets.clear();
	preciseBdds.clear();
	preciseBvecs.clear();
	sameBWPreciseBdds.clear();
	sameBWPreciseBvecs.clear();
    }

    z3::expr expression;
    BDD Proccess();

    Approximated<BDD> ProcessUnderapproximation(int, unsigned int);
    Approximated<BDD> ProcessOverapproximation(int, unsigned int);

    std::map<std::string, BDD> GetVarSets() { return varSets; }

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
		  bddManager.SetSiftMaxVar(100);
                  bddManager.AutodynEnable(CUDD_REORDER_SIFT);
                  break;
              case SIFT_ITE:
		  bddManager.SetMaxGrowth(1.05);
		  bddManager.SetSiftMaxVar(100);
		  bddManager.AutodynEnable(CUDD_REORDER_SIFT_CONVERGE);
                  break;
              default:
                  break;
          }
	}
    }

    void PrintModel(const BDD&);
    std::map<std::string, std::vector<bool>> GetModel(const BDD&);
};

#endif
