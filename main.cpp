#include <iostream>
#include <string>
#include <z3++.h>
#include <bdd.h>
#include <cmath>
#include <fstream>

#include "ExprToBDDTransformer.h"
#include "ExprSimplifier.h"

using namespace std;
using namespace z3;

enum Result { SAT, UNSAT };

void set_bdd()
{
    if (bdd_isrunning())
    {
        bdd_done();
    }

    bdd_init(1000000,100000);
    bdd_setcacheratio(10);
}

Result run(z3::expr &e)
{
    set_bdd();

    ExprToBDDTransformer transformer(e.ctx(), e);

    bdd returned = transformer.Proccess();
    return (returned.id() == 0 ? UNSAT : SAT);
}

Result runString(const char* input)
{
    set_bdd();

    z3::context ctx;
    Z3_ast ast = Z3_parse_smtlib2_string(ctx, (Z3_string)input, 0, 0, 0, 0, 0, 0);

    expr e = to_expr(ctx, ast);
    //cout << Z3_get_smtlib_error(ctx) << endl;

    ExprToBDDTransformer transformer(e.ctx(), e);

    bdd returned = transformer.Proccess();
    return (returned.id() == 0 ? UNSAT : SAT);
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

Result runOverapproximation(z3::expr &e, int bitWidth)
{
    set_bdd();

    ExprToBDDTransformer transformer(e.ctx(), e);
    transformer.setApproximationType(SIGN_EXTEND);

    bdd returned = transformer.ProcessOverapproximation(bitWidth);
    return (returned.id() == 0 ? UNSAT : SAT);
}

Result runUnderApproximation(z3::expr &e, int bitWidth)
{
    set_bdd();

    ExprToBDDTransformer transformer(e.ctx(), e);
    transformer.setApproximationType(ZERO_EXTEND);

    cout << "Underapproximating " << bitWidth << endl;
    bdd returned = transformer.ProcessUnderapproximation(bitWidth);
    return (returned.id() == 0 ? UNSAT : SAT);
}

void runWithApproximations(z3::expr &e)
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    for (int i = 1; i < 32; i = i*2)
    {
        cout << endl << endl << "overapproximation " << i << endl;
        Result overApproxResult = runOverapproximation(e, i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "overapproximation " << i << endl;
            cout << "unsat" << endl;
            exit(0);
        }

        cout << endl << endl << "overapproximation " << i << endl;
        overApproxResult = runOverapproximation(e, -i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "overapproximation " << -i << endl;
            cout << "unsat" << endl;
            exit(0);
        }

        cout << "underapproximation " << i << endl;
        Result underApproxResult = runUnderApproximation(e, i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "underapproximation " << i << endl;
            cout << "sat" << endl;
            exit(0);
        }

        cout << "underapproximation " << i << endl;
        underApproxResult = runUnderApproximation(e, -i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "underapproximation " << -i << endl;
            cout << "sat" << endl;
            exit(0);
        }
    }

    Result result = run(e);
    cout << "-------------------------" << endl;
    cout << (result == SAT ? "sat" : "unsat") << endl;
}

void runWithUnderApproximations(z3::expr &e)
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    for (int i = 1; i < 32; i = i*2)
    {
        cout << "underapproximation " << i << endl;
        Result underApproxResult = runUnderApproximation(e, i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "underapproximation " << i << endl;
            cout << "sat" << endl;
            exit(0);
        }

        cout << "underapproximation " << i << endl;
        underApproxResult = runUnderApproximation(e, -i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "underapproximation " << -i << endl;
            cout << "sat" << endl;
            exit(0);
        }
    }

    Result result = run(e);
    cout << "-------------------------" << endl;
    cout << (result == SAT ? "sat" : "unsat") << endl;
}

void runWithOverApproximations(z3::expr &e)
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    for (int i = 1; i < 32; i = i*2)
    {
        cout << endl << endl << "overapproximation " << i << endl;
        Result overApproxResult = runOverapproximation(e, i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "overapproximation " << i << endl;
            cout << "unsat" << endl;
            exit(0);
        }

        cout << endl << endl << "overapproximation " << i << endl;
        overApproxResult = runOverapproximation(e, -i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "overapproximation " << -i << endl;
            cout << "unsat" << endl;
            exit(0);
        }
    }

    Result result = run(e);
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

  z3::context ctx;
  Z3_ast ast = Z3_parse_smtlib2_file(ctx, argv[1], 0, 0, 0, 0, 0, 0);
  expr e = to_expr(ctx, ast);

  ExprSimplifier simplifier(ctx);
  e = simplifier.Simplify(e);

  if (argc > 3 && argv[2] == std::string("-o"))
  {
      Result result = runOverapproximation(e, atoi(argv[3]));
      cout << "-------------------------" << endl;
      cout << (result == SAT ? "unknown" : "unsat") << endl;
  }
  else if (argc > 3 && argv[2] == std::string("-u"))
  {
      Result result = runUnderApproximation(e, atoi(argv[3]));
      cout << "-------------------------" << endl;
      cout << (result == SAT ? "sat" : "unknown") << endl;
  }
  else if (argc > 2 && argv[2] == std::string("--try-approximations"))
  {
    cout << "Trying approximations" << endl;
    runWithApproximations(e);
  }
  else if (argc > 2 && argv[2] == std::string("--try-underapproximations"))
  {
    cout << "Trying underapproximations" << endl;
    runWithUnderApproximations(e);
  }
  else if (argc > 2 && argv[2] == std::string("--try-overapproximations"))
  {
    cout << "Trying overapproximations" << endl;
    runWithOverApproximations(e);
  }
  else if (argc > 2 && argv[2] == std::string("--application"))
  {
    runApplication(argv[1]);
  }
  else
  {
      Result result = run(e);
      cout << (result == SAT ? "sat" : "unsat") << endl;
  }

  return 0;
}
