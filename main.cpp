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
    int i = 0;
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

            stringstream ss;
            ss << "file" << i << ".smt2";

            ofstream outfile;
            outfile.open(ss.str());
            outfile << toCheck << "\n(check-sat)";
            outfile.close();

            std::cout << "file written" << std::endl;
            i++;

            //Result result = runString(toCheck.c_str());
            //cout << (result == SAT ? "sat" : "unsat") << endl;
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
          {"initial-order", required_argument, 0, 'i' },
          {0,           0,                 0,  0   }
  };

  bool applicationFlag = false, tryOverFlag = false, tryUnderFlag = false, propagateUnconstrainedFlag = false;
  int underApproximation = 0, overApproximation = 0;  
  char* filename;
  ReorderType reorderType = SIFT;
  InitialOrder initialOrder = HEURISTIC;

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
               else if (optionString == "none")
               {
                   reorderType = NO_REORDER;
               }
               else
               {
                   std::cout << "Invalid reorder type" << std::endl;
                   exit(1);
               }

               break;
           }
           case 'i':
           {
               string optionString(optarg);

               if (optionString == "heuristic")
               {
                   initialOrder = HEURISTIC;
               }
               else if (optionString == "sequential")
               {
                   initialOrder = SEQUENTIAL;
               }
               else if (optionString == "interleave")
               {
                   initialOrder = INTERLEAVE_ALL;
               }
               else
               {
                   std::cout << "Invalid initial order type" << std::endl;
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
      return 1;
  }

  if (applicationFlag)
  {
      std::cout << "Application: " << filename << std::endl;
      runApplication(filename);
      return 0;
  }

  z3::context ctx;
  Z3_ast ast = Z3_parse_smtlib2_file(ctx, filename, 0, 0, 0, 0, 0, 0);
  expr e = to_expr(ctx, ast);

  std::cout << "Processing " << filename << std::endl;
  Solver solver(propagateUnconstrainedFlag);
  solver.SetInitialOrder(initialOrder);

  solver.SetReorderType(reorderType);

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

  Result result = solver.GetResult(e);
  cout << (result == SAT ? "sat" : result == UNSAT ? "unsat" : "unknown") << endl;

  return 0;
}
