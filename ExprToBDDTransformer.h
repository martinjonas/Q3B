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

  public:
    ExprToBDDTransformer(z3::context &ctx, z3::expr e) : expression(e) 
    {       
      this->context = &ctx;

      z3::params simplifyParams(ctx);
      simplifyParams.set(":blast_distinct", true);
      simplifyParams.set(":elim_sign_ext", true);
      //simplifyParams.set(":blast_eq_value", false);
      //simplifyParams.set(":flat", false);
      simplifyParams.set(":pull_cheap_ite", true);
      simplifyParams.set(":ite_extra_rules", true);

      z3::goal g(ctx);
      g.add(expression);
      z3::tactic simplifyTactic =
              with(z3::tactic(ctx, "simplify"), simplifyParams);
     
      z3::apply_result result = simplifyTactic(g);
      //std::cout << result[0] << std::endl;
      
      z3::goal simplified = result[0];
      expression = simplified.as_expr();

      std::cout << expression << std::endl;

      ExprSimplifier simplifier(ctx);
      expression = simplifier.Simplify(expression);
      //std::cout << "substituted:" << std::endl;
      //std::cout << expression << std::endl;

      z3::goal g2(ctx);
      g2.add(expression);

      z3::tactic derTactic = simplifyTactic &
              z3::tactic(ctx, "elim-and") &
              z3::tactic(ctx, "der") &
              simplifyTactic;      

      z3::apply_result result2 = derTactic(g2);
      //std::cout << result[0] << std::endl;
      //std::cout << result2 << std::endl;

      z3::goal simplified2 = result2[0];
      expression = simplified2.as_expr();

      std::cout << "simplified:" << std::endl;
      std::cout << expression << std::endl;

      //expression = e;
      ctx.check_error();
      //std::cout << simplifyParams;
      
      loadVars();
    }
    void PrintVars();
    bdd Proccess();
    std::map<std::string, bdd> GetVarSets() { return varSets; }
};

#endif
