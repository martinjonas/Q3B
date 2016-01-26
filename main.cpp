#include <iostream>
#include <string>
#include <z3++.h>
#include <bdd.h>
#include <cmath>
#include <fstream>
#include <getopt.h>

#include <chrono>

#include "ExprToBDDTransformer.h"
#include "ExprSimplifier.h"

using namespace std;
using namespace z3;

using std::chrono::high_resolution_clock;
using std::chrono::milliseconds;

enum Result { SAT, UNSAT };

ExprToBDDTransformer *transformer;

void set_bdd()
{
    if (bdd_isrunning())
    {
        bdd_done();
    }

    //auto t0 = high_resolution_clock::now();

    //bdd_init(200000,40000);
    //bdd_setcacheratio(5);

    bdd_init(400000,100000);
    //bdd_setcacheratio(5);
    bdd_gbc_hook(NULL);
    //bdd_reorder_verbose(1);

    //auto t1 = high_resolution_clock::now();
    //milliseconds total_ms = std::chrono::duration_cast<milliseconds>(t1 - t0);
    //std::cout << "bdd init: " << total_ms.count() << " miliseconds"  << std::endl;
}

Result run()
{
    bdd returned = transformer->Proccess();
    Result result = (returned.id() == 0 ? UNSAT : SAT);

    return result;
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

Result runOverApproximation(int bitWidth)
{
    transformer->setApproximationType(SIGN_EXTEND);

    bdd returned = transformer->ProcessOverapproximation(bitWidth);
    return (returned.id() == 0 ? UNSAT : SAT);
}

Result runUnderApproximation(int bitWidth)
{
    transformer->setApproximationType(ZERO_EXTEND);

    bdd returned = transformer->ProcessUnderapproximation(bitWidth);
    return (returned.id() == 0 ? UNSAT : SAT);
}

void runWithApproximations()
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    for (int i = 1; i < 32; i = i*2)
    {
        cout << endl << endl << "overapproximation " << i << endl;
        Result overApproxResult = runOverApproximation(i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "overapproximation " << i << endl;
            cout << "unsat" << endl;
            exit(0);
        }

        cout << endl << endl << "overapproximation -" << i << endl;
        overApproxResult = runOverApproximation(-i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "overapproximation " << -i << endl;
            cout << "unsat" << endl;
            exit(0);
        }

        cout << "underapproximation " << i << endl;
        Result underApproxResult = runUnderApproximation(i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "underapproximation " << i << endl;
            cout << "sat" << endl;
            exit(0);
        }

        cout << "underapproximation " << i << endl;
        underApproxResult = runUnderApproximation(-i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "underapproximation " << -i << endl;
            cout << "sat" << endl;
            exit(0);
        }
    }

    Result result = run();
    cout << "-------------------------" << endl;
    cout << (result == SAT ? "sat" : "unsat") << endl;
}

void runWithUnderApproximations()
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    int i = 1;

    cout << "underapproximation " << i << endl;
    Result underApproxResult = runUnderApproximation(i);
    if (underApproxResult == SAT)
    {
        cout << "-------------------------" << endl;
        cout << "Reason: underapproximation " << i << endl;
        cout << "sat" << endl;
        exit(0);
    }

    cout << "underapproximation " << i << endl;
    underApproxResult = runUnderApproximation(-i);
    if (underApproxResult == SAT)
    {
        cout << "-------------------------" << endl;
        cout << "Reason: underapproximation " << -i << endl;
        cout << "sat" << endl;
        exit(0);
    }

    for (int i = 2; i < 32; i = i+2)
    {
        cout << "underapproximation " << i << endl;
        Result underApproxResult = runUnderApproximation(i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "Reason: underapproximation " << i << endl;
            cout << "sat" << endl;
            exit(0);
        }

        cout << "underapproximation " << i << endl;
        underApproxResult = runUnderApproximation(-i);
        if (underApproxResult == SAT)
        {
            cout << "-------------------------" << endl;
            cout << "Reason: underapproximation " << -i << endl;
            cout << "sat" << endl;
            exit(0);
        }
    }

    cout << "-------------------------" << endl;
    cout << "unknown" << endl;
}

void runWithOverApproximations()
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    int i = 1;

    cout << endl << endl << "overapproximation " << i << endl;
    Result overApproxResult = runOverApproximation(i);
    if (overApproxResult == UNSAT)
    {
        cout << "-------------------------" << endl;
        cout << "Reason: overapproximation " << i << endl;
        cout << "unsat" << endl;
        exit(0);
    }

    cout << endl << endl << "overapproximation -" << i << endl;
    overApproxResult = runOverApproximation(-i);
    if (overApproxResult == UNSAT)
    {
        cout << "-------------------------" << endl;
        cout << "Reason: overapproximation " << -i << endl;
        cout << "unsat" << endl;
        exit(0);
    }

    for (i = 2; i < 32; i = i+2)
    {
        cout << endl << endl << "overapproximation " << i << endl;
        Result overApproxResult = runOverApproximation(i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "Reason: overapproximation " << i << endl;
            cout << "unsat" << endl;
            exit(0);
        }

        cout << endl << endl << "overapproximation " << i << endl;
        overApproxResult = runOverApproximation(-i);
        if (overApproxResult == UNSAT)
        {
            cout << "-------------------------" << endl;
            cout << "Reason: overapproximation " << -i << endl;
            cout << "unsat" << endl;
            exit(0);
        }
    }

    cout << "-------------------------" << endl;
    cout << "unknown" << endl;
}

int main(int argc, char* argv[])
{
  static struct option long_options[] = {
          {"overapproximation", required_argument, 0, 'o' },
          {"underapproximation", required_argument, 0, 'u' },
          {"try-overapproximations", no_argument, 0, 'O' },
          {"try-underapproximations", no_argument, 0, 'U' },
          {"application", no_argument, 0, 'a' },
          {"reorder", required_argument, 0, 'r' },
          {"propagate-unconstrained", no_argument, 0, 'p' },
          {0,           0,                 0,  0   }
  };

  bool applicationFlag = false, tryOverFlag = false, tryUnderFlag = false, propagateUnconstrainedFlag = false;
  int underApproximation = 0, overApproximation = 0;  
  char* filename;
  ReorderType reorderType = NO_REORDER;

  int opt = 0;

  int long_index = 0;
  while ((opt = getopt_long(argc, argv,"o:u:OUar:", long_options, &long_index )) != -1) {
     switch (opt) {
           case 'a':
               applicationFlag = true;
               break;
           case 'o':
               overApproximation = atoi(optarg);
               break;
           case 'u':
               underApproximation = atoi(optarg);
               break;
           case 'O':
                tryOverFlag = true;
                break;
           case 'U':
               tryUnderFlag = true;
               break;
            case 'p':
               propagateUnconstrainedFlag = true;
               break;
           case 'r':
           {
               string optionString(optarg);

               if (optionString == "win2")
               {
                   reorderType = WIN2;
               }
               else if (optionString == "win2ite")
               {
                   reorderType = WIN2_ITE;
               }
               else if (optionString == "win3")
               {
                   reorderType = WIN3;
               }
               else if (optionString == "win3ite")
               {
                   reorderType = WIN3_ITE;
               }
               else if (optionString == "sift")
               {
                   reorderType = SIFT;
               }
               else if (optionString == "siftite")
               {
                   reorderType = SIFT_ITE;
               }
               else
               {
                   std::cout << "Invalid reorder type" << std::endl;
                   exit(1);
               }

               break;
           }
           default:
               std::cout << "Invalid arguments" << std::endl;
               exit(1);
               //print_usage();
      }
  }

  if (optind < argc)
  {
      filename = argv[optind];
  }
  else
  {
      std::cout << "Filename required" << std::endl;
      abort();
  }

  z3::context ctx;
  Z3_ast ast = Z3_parse_smtlib2_file(ctx, filename, 0, 0, 0, 0, 0, 0);
  expr e = to_expr(ctx, ast);

  ExprSimplifier simplifier(ctx, propagateUnconstrainedFlag);
  e = simplifier.Simplify(e);

  if (e.is_const())
  {
      std::stringstream ss;
      ss << e;
      if (ss.str() == "true")
      {
          std::cout << "Reason: simplification" << std::endl;
          cout << "-------------------------" << endl;
          cout << "sat" << endl;
          return 0;
      }
      else if (ss.str() == "false")
      {
          std::cout << "Reason: simplification" << std::endl;
          cout << "-------------------------" << endl;
          cout << "unsat" << endl;
          return 0;
      }
  }

  set_bdd();

  std::cout << "Processing " << filename << std::endl;
  transformer = new ExprToBDDTransformer(e.ctx(), e);  

  if (reorderType != NO_REORDER)
  {
      transformer->setReorderType(reorderType);
  }

  if (overApproximation != 0)
  {
      Result result = runOverApproximation(overApproximation);
      cout << "-------------------------" << endl;
      cout << (result == SAT ? "unknown" : "unsat") << endl;
  }
  else if (underApproximation != 0)
  {
      Result result = runUnderApproximation(underApproximation);
      cout << "-------------------------" << endl;
      cout << (result == SAT ? "sat" : "unknown") << endl;
  }
  else if (tryOverFlag)
  {
    cout << "Trying overapproximations" << endl;
    runWithOverApproximations();
  }
  else if (tryUnderFlag)
  {
    cout << "Trying underapproximations" << endl;
    runWithUnderApproximations();
  }
  else if (applicationFlag)
  {
    runApplication(filename);
  }
  else
  {
      Result result = run();
      cout << (result == SAT ? "sat" : "unsat") << endl;
  }

  return 0;
}
