#ifndef ExprToBDDTransformer_h
#define ExprToBDDTransformer_h

#include <string>
#include <set>
#include <vector>
#include <map>
#include <bdd.h>
#include <bvec.h>
#include <fdd.h>
#include <z3++.h>
#include "ExprSimplifier.h"

typedef std::pair<std::string, int> var;

enum BoundType { EXISTENTIAL, UNIVERSAL };
enum ApproximationType { ZERO_EXTEND, SIGN_EXTEND };

typedef std::pair<std::string, BoundType> boundVar;

class ExprToBDDTransformer
{
  private:
    std::map<std::string, bvec> vars;
    std::map<std::string, bdd> varSets;
    bdd m_bdd;

    z3::context* context;
    //std::map<std::string, int> varToBddIndex;

    z3::expr expression;
    int bv_size = 16;

    std::set<var> getConsts(const z3::expr &e) const;
    std::set<var> getBoundVars(const z3::expr &e) const;
    void loadVars();    
    
    void loadBDDsFromExpr(z3::expr);
    bdd getBDDFromExpr(z3::expr, std::vector<boundVar> boundVars);
    bvec getBvecFromExpr(z3::expr, std::vector<boundVar> boundVars);

    unsigned int getNumeralValue(const z3::expr);
    bvec getNumeralBvec(const z3::expr);
    void applyDer();
    void distributeForall();

    bdd getConjunctionBdd(const std::vector<z3::expr> &, const std::vector<boundVar>&);
    bdd getDisjunctionBdd(const std::vector<z3::expr> &, const std::vector<boundVar>&);

    int exisentialBitWidth;
    int universalBitWidth;
    ApproximationType approximationType;

  public:
    ExprToBDDTransformer(z3::context&, z3::expr);
    void PrintVars();
    bdd Proccess();

    bdd ProcessUnderapproximation(int);
    bdd ProcessOverapproximation(int);

    std::map<std::string, bdd> GetVarSets() { return varSets; }       

    void setApproximationType(ApproximationType at)
    {
        approximationType = at;
    }
};

#endif
