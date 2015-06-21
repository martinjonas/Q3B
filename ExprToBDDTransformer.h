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
    bvec allocBvec(int);
    
    void loadBDDsFromExpr(z3::expr);
    bdd getBDDFromExpr(z3::expr, std::vector<std::string> boundVars);
    bvec getBvecFromExpr(z3::expr, std::vector<std::string> boundVars);

    int getNumeralValue(const z3::expr);
    void applyDer();

  public:
    ExprToBDDTransformer(z3::context&, z3::expr);
    void PrintVars();
    bdd Proccess();
    std::map<std::string, bdd> GetVarSets() { return varSets; }
};

#endif
