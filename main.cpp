#include <iostream>
#include <string>
#include <z3++.h>
#include <set>
#include <map>
#include <bdd.h>
#include <bvec.h>
#include <cmath>

#include <future>
#include <chrono>

#include "ExprToBDDTransformer.h"

using namespace std;
using namespace z3;

void run(char* fileName)
{
    bdd_init(1000000,10000);
    context ctx;

    Z3_ast ast = Z3_parse_smtlib2_file(ctx, fileName, 0, 0, 0, 0, 0, 0);

    //Z3_ast_kind k = ast->kind();
    //cout << (ast->kind() == Z3_FUNC_DECL_AST)  << endl;
    //Z3_string s = Z3_ast_to_string(z3ctx, ast);

    expr e = to_expr(ctx, ast);
    cout << Z3_get_smtlib_error(ctx) << endl;
    //cout << e.simplify() << endl;
    //cout << ast.kind() << endl;
    //visit(e);
    ExprToBDDTransformer transformer(ctx, e);
    //transformer.PrintVars();
    //bdd eBdd = transformer.GetBDD();

    bdd returned = transformer.Proccess();
    //bdd_printtable(returned);

    double satCount = bdd_satcountset(returned, bdd_ithvar(0));
    //double satCount = bdd_satcount(returned);

    //bdd satOne = bdd_fullsatone(returned);
    //bdd_printset(satOne);

    //std::map<std::string, bdd> varSets = transformer.GetVarSets();
    //for (auto &varSet : varSets)
    //{
    //    cout << varSet.first << endl;
    //
    //}
    //bdd sat = bdd_satoneset(returned, bdd_true(), bdd_false());
    //bdd_printset(sat);
    //cout << endl << endl;

    cout << "---------------------------------------" << endl;
    //cout << "SAT COUNT: " << satCount << endl;
    cout << (satCount < 0.5 ? "unsat" : "sat") << endl;
}

int main(int argc, char* argv[])
{
  if (argc < 2)
  {
    cout << "Expected file name";
    return 0;
  }

  run(argv[1]);
  //bdd_fnprintdot("bdd.dot", transformer.);

  return 0;
}
