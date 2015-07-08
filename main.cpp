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

#include <fstream>

#include "ExprToBDDTransformer.h"

using namespace std;
using namespace z3;

enum Result { SAT, UNSAT };

Result run(char* fileName)
{
    bdd_done();
    bdd_init(1000000,10000);
    bdd_setcacheratio(10);
    context ctx;

    Z3_ast ast = Z3_parse_smtlib2_file(ctx, fileName, 0, 0, 0, 0, 0, 0);    

    expr e = to_expr(ctx, ast);
    cout << Z3_get_smtlib_error(ctx) << endl;

    ExprToBDDTransformer transformer(ctx, e);

    bdd returned = transformer.Proccess();

    double satCount = bdd_satcountset(returned, bdd_ithvar(0));

    return (satCount < 0.5 ? UNSAT : SAT);
}

Result runString(const char* input)
{
    bdd_done();
    bdd_init(1000000,10000);
    bdd_setcacheratio(10);
    context ctx;

    Z3_ast ast = Z3_parse_smtlib2_string(ctx, (Z3_string)input, 0, 0, 0, 0, 0, 0);

    expr e = to_expr(ctx, ast);
    //cout << Z3_get_smtlib_error(ctx) << endl;

    ExprToBDDTransformer transformer(ctx, e);

    bdd returned = transformer.Proccess();

    double satCount;
    if (bdd_varnum() == 0)
    {
        satCount = bdd_satcount(returned);
    }
    else
    {
        satCount = bdd_satcountset(returned, bdd_ithvar(0));
    }


    return (satCount < 0.5 ? UNSAT : SAT);
}

void runApplication(char* fileName)
{
    std::ifstream file(fileName);
    std::vector<std::string> stack;
    stack.push_back("");

    std::string line;
    while (std::getline(file, line))
    {
        if (line.find("(declare") == 0 || line.find("(assert") == 0)
        {
            std::string top = stack[stack.size() - 1];
            stack.pop_back();
            stack.push_back(top + "\n" + line);
        }
        else if (line.find("(pop 1)") == 0)
        {
            stack.pop_back();
        }
        else if (line.find("(push 1)") == 0)
        {
            stack.push_back("");
        }
        else if (line.find("(echo") == 0)
        {
            cout << line.substr(7, line.length() - 10) << endl;
        }
        else if (line.find("(check-sat)") == 0)
        {
            std::string toCheck = "";
            for (std::string &s : stack)
            {
                toCheck += "\n" + s;
            }

            Result result = runString(toCheck.c_str());
            cout << (result == SAT ? "sat" : "unsat") << endl;
        }
    }

    file.close();
}

Result runOverapproximation(char* fileName, int bitWidth)
{
    bdd_done();
    bdd_init(1000000,10000);
    bdd_setcacheratio(10);
    context ctx;

    Z3_ast ast = Z3_parse_smtlib2_file(ctx, fileName, 0, 0, 0, 0, 0, 0);

    expr e = to_expr(ctx, ast);
    cout << Z3_get_smtlib_error(ctx) << endl;

    ExprToBDDTransformer transformer(ctx, e);

    bdd returned = transformer.ProcessOverapproximation(bitWidth);

    double satCount = bdd_satcountset(returned, bdd_ithvar(0));

    return (satCount < 0.5 ? UNSAT : SAT);
}

Result runUnderApproximation(char* fileName, int bitWidth)
{
    bdd_done();
    bdd_init(1000000,10000);
    bdd_setcacheratio(10);
    context ctx;

    Z3_ast ast = Z3_parse_smtlib2_file(ctx, fileName, 0, 0, 0, 0, 0, 0);

    expr e = to_expr(ctx, ast);
    cout << Z3_get_smtlib_error(ctx) << endl;

    ExprToBDDTransformer transformer(ctx, e);

    cout << "Underapproximating " << bitWidth << endl;
    bdd returned = transformer.ProcessUnderapproximation(bitWidth);

    double satCount = bdd_satcountset(returned, bdd_ithvar(0));
    return (satCount < 0.5 ? UNSAT : SAT);
}

void runWithApproximations(char* fileName)
{
    for (int i = 1; i < 32; i = i*2)
    {
        cout << endl << endl << "overapproximation " << i << endl;
        Result overApproxResult = runOverapproximation(fileName, i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "overapproximation " << i << endl;
            cout << "unsat" << endl;
            exit(0);
        }

        cout << endl << endl << "overapproximation " << i << endl;
        overApproxResult = runOverapproximation(fileName, -i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "overapproximation " << -i << endl;
            cout << "unsat" << endl;
            exit(0);
        }

        cout << "underapproximation " << i << endl;
        Result underApproxResult = runUnderApproximation(fileName, i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "underapproximation " << i << endl;
            cout << "sat" << endl;
            exit(0);
        }

        cout << "underapproximation " << i << endl;
        underApproxResult = runUnderApproximation(fileName, -i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "underapproximation " << -i << endl;
            cout << "sat" << endl;
            exit(0);
        }
    }

    Result result = run(fileName);
    cout << "-------------------------" << endl;
    cout << (result == SAT ? "sat" : "unsat") << endl;
}

int main(int argc, char* argv[])
{  
  if (argc < 2)
  {
    cout << "Expected file name";
    return 0;
  }

  bdd_init(1000000,10000);
  bdd_setcacheratio(10);

  if (argc > 3 && argv[2] == std::string("-o"))
  {
      Result result = runOverapproximation(argv[1], atoi(argv[3]));
      cout << "-------------------------" << endl;
      cout << (result == SAT ? "unknown" : "unsat") << endl;
  }
  else if (argc > 3 && argv[2] == std::string("-u"))
  {
      Result result = runUnderApproximation(argv[1], atoi(argv[3]));
      cout << "-------------------------" << endl;
      cout << (result == SAT ? "sat" : "unknown") << endl;
  }
  else if (argc > 2 && argv[2] == std::string("-approx"))
  {
    cout << "approximations" << endl;
    runWithApproximations(argv[1]);
  }
  else if (argc > 2 && argv[2] == std::string("-application"))
  {
    runApplication(argv[1]);
  }
  else
  {
      Result result = run(argv[1]);
      cout << "-------------------------" << endl;
      cout << (result == SAT ? "sat" : "unsat") << endl;
  }
  //bdd_fnprintdot("bdd.dot", transformer.);

  return 0;
}
