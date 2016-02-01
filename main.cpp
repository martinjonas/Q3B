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
#include "Solver.h"

using namespace std;
using namespace z3;

using std::chrono::high_resolution_clock;
using std::chrono::milliseconds;

ExprToBDDTransformer *transformer;

Result runString(const char* input)
{    
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

  std::cout << "Processing " << filename << std::endl;
  Solver solver(propagateUnconstrainedFlag);

  if (reorderType != NO_REORDER)
  {
      solver.SetReorderType(reorderType);
  }
  else
  {
      solver.SetReorderType(SIFT);
  }

  if (overApproximation != 0)
  {
      solver.SetApproximation(OVERAPPROXIMATION, overApproximation);
  }
  else if (underApproximation != 0)
  {
      solver.SetApproximation(UNDERAPPROXIMATION, overApproximation);
  }
  else if (tryOverFlag)
  {
    cout << "Trying overapproximations" << endl;
    solver.SetApproximation(OVERAPPROXIMATION, 0);
  }
  else if (tryUnderFlag)
  {
    cout << "Trying underapproximations" << endl;
    solver.SetApproximation(UNDERAPPROXIMATION, 0);
  }
  else if (applicationFlag)
  {
    runApplication(filename);
  }

  Result result = solver.GetResult(e);
  cout << (result == SAT ? "sat" : result == UNSAT ? "unsat" : "unknown") << endl;

  return 0;
}
