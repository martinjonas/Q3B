#ifndef ExprToBDDTransformer_h
#define ExprToBDDTransformer_h

#include <string>
#include <set>
#include <vector>
#include <map>
#include <unordered_map>
#include "cudd.h"
#include <cuddObj.hh>
#include "../BDD/cudd/bvec_cudd.h"
#include <z3++.h>
#include "ExprSimplifier.h"
#include "VariableOrderer.h"

typedef std::pair<std::string, int> var;

enum BoundType { EXISTENTIAL, UNIVERSAL };
enum ApproximationType { ZERO_EXTEND, SIGN_EXTEND };
enum ApproximationMethod { NONE, VARIABLES, OPERATIONS, BOTH };
enum ReorderType { NO_REORDER, WIN2, WIN2_ITE, WIN3, WIN3_ITE, SIFT, SIFT_ITE };
enum InitialOrder { INTERLEAVE_ALL, HEURISTIC, SEQUENTIAL };
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

    std::map<const Z3_ast, std::pair<BDD, std::vector<boundVar>>> bddExprCache;
    std::map<const Z3_ast, std::pair<BDD, std::vector<boundVar>>> preciseResults;
    std::map<const Z3_ast, std::pair<Bvec, std::vector<boundVar>>> bvecExprCache;

    std::set<Z3_ast> processedVarsCache;

    z3::context* context;
    //std::map<std::string, int> varToBddIndex;

    z3::expr expression;

    void getVars(const z3::expr &e);
    void loadVars();

    BDD loadBDDsFromExpr(z3::expr);
    bool correctBoundVars(const std::vector<boundVar> &, const std::vector<boundVar>&);
    BDD getBDDFromExpr(const z3::expr&, std::vector<boundVar>, bool onlyExistentials, bool isPositive);
    Bvec getApproximatedVariable(const std::string&, int, const ApproximationType&);
    Bvec getBvecFromExpr(const z3::expr&, std::vector<boundVar>);

    unsigned int getNumeralValue(const z3::expr&);
    unsigned int getNumeralOnes(const z3::expr&);
    Bvec getNumeralBvec(const z3::expr&);

    BDD getConjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bool, bool);
    BDD getDisjunctionBdd(const std::vector<z3::expr>&, const std::vector<boundVar>&, bool, bool);

    int approximation;
    int variableBitWidth;

    unsigned int operationPrecision;

    ApproximationType approximationType;
    ApproximationMethod approximationMethod;
    ReorderType reorderType = NO_REORDER;
    InitialOrder initialOrder = HEURISTIC;
    bool m_negateMul;
    bool m_limitBddSizes = false;

    bool variableApproximationHappened = false;
    bool operationApproximationHappened = false;

    int cacheHits = 0;

    Cudd bddManager;

    Bvec bvneg(Bvec bv, int bitSize);
    Bvec bvec_mul(Bvec&, Bvec&);

    BDD m_dontCare;
    BDD applyDontCare(BDD);
    Bvec applyDontCare(Bvec);

  public:
    ExprToBDDTransformer(z3::context& context, z3::expr e) : ExprToBDDTransformer(context, e, HEURISTIC) {}
    ExprToBDDTransformer(z3::context& context, z3::expr e, InitialOrder initialOrder);

    ~ExprToBDDTransformer()
    {
	vars.clear();
	varSets.clear();
	preciseResults.clear();
    }

    BDD Proccess();

    BDD ProcessUnderapproximation(int, unsigned int);
    BDD ProcessOverapproximation(int, unsigned int);

    std::map<std::string, BDD> GetVarSets() { return varSets; }

    void setApproximationType(ApproximationType at)
    {
        approximationType = at;
    }

    void setApproximationMethod(ApproximationMethod am)
    {
        approximationMethod = am;
    }

    void SetNegateMul(bool negateMul)
    {
	m_negateMul = negateMul;
    }

    void SetLimitBddSizes(bool limitBddSizes)
    {
	m_limitBddSizes = limitBddSizes;
    }

    void SetDontCare(BDD dontCare)
    {
	m_dontCare = dontCare;
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

    void setReorderType(ReorderType rt)
    {
        reorderType = rt;

        if (reorderType != NO_REORDER)
        {
          switch (reorderType)
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
};

#endif
