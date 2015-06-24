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

    expr e = to_expr(ctx, ast);
    cout << Z3_get_smtlib_error(ctx) << endl;

    ExprToBDDTransformer transformer(ctx, e);    

    bdd returned;

    double satCount = bdd_satcountset(returned, bdd_ithvar(0));

    cout << "---------------------------------------" << endl;
    //cout << "SAT COUNT: " << satCount << endl;
    cout << (satCount < 0.5 ? "unsat" : "sat") << endl;
}

void runOverapproximation(char* fileName, int bitWidth)
{
    bdd_init(1000000,10000);
    context ctx;

    Z3_ast ast = Z3_parse_smtlib2_file(ctx, fileName, 0, 0, 0, 0, 0, 0);

    expr e = to_expr(ctx, ast);
    cout << Z3_get_smtlib_error(ctx) << endl;

    ExprToBDDTransformer transformer(ctx, e);

    bdd returned = transformer.ProcessOverapproximation(bitWidth);

    double satCount = bdd_satcountset(returned, bdd_ithvar(0));

    cout << "---------------------------------------" << endl;
    cout << "OVERAPPROXIMATION" << endl;
    //cout << "SAT COUNT: " << satCount << endl;
    cout << (satCount < 0.5 ? "unsat" : "sat") << endl;
}

void runUnderApproximation(char* fileName, int bitWidth)
{
    bdd_init(1000000,10000);
    context ctx;

    Z3_ast ast = Z3_parse_smtlib2_file(ctx, fileName, 0, 0, 0, 0, 0, 0);

    expr e = to_expr(ctx, ast);
    cout << Z3_get_smtlib_error(ctx) << endl;

    ExprToBDDTransformer transformer(ctx, e);

    bdd returned = transformer.ProcessUnderapproximation(bitWidth);

    double satCount = bdd_satcountset(returned, bdd_ithvar(0));

    cout << "---------------------------------------" << endl;
    cout << "UNDERAPPROXIMATION" << endl;
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

  if (argc > 3 && argv[2] == std::string("-o"))
  {
      runOverapproximation(argv[1], atoi(argv[3]));
  }
  else if (argc > 3 && argv[2] == std::string("-u"))
  {
      runUnderApproximation(argv[1], atoi(argv[3]));
  }
  else
  {
    run(argv[1]);
  }
  //bdd_fnprintdot("bdd.dot", transformer.);

  return 0;
}
