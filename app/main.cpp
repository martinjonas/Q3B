#include <iostream>
#include <string>
#include <z3++.h>
#include "cudd.h"
#include <cuddObj.hh>
#include <fstream>
#include <getopt.h>

#include "../lib/Solver.h"
#include "../lib/Logger.h"
#include "../lib/Config.h"

using namespace std;
using namespace z3;

using std::chrono::high_resolution_clock;
using std::chrono::milliseconds;

int main(int argc, char* argv[])
{
    static struct option long_options[] = {
	{"overapproximation", required_argument, 0, 'o' },
	{"underapproximation", required_argument, 0, 'u' },
	{"try-overapproximations", no_argument, 0, 'O' },
	{"try-underapproximations", no_argument, 0, 'U' },
	{"try-approximations", no_argument, 0, 'A' },
	{"approximation-method", required_argument, 0, 'm' },
	{"reorder", required_argument, 0, 'r' },
	{"propagate-unconstrained", no_argument, 0, 'p' },
	{"initial-order", required_argument, 0, 'i' },
	{"with-dont-cares", no_argument, 0, 'd' },
	{"check-models", no_argument, 0, 'c' },
	{"flip-universal", no_argument, 0, 'f' },
	{"necessary-bits", no_argument, 0, 'b' },
        {"goal-unconstrained", no_argument, 0, 'g' },
	{0,           0,                 0,  0   }
    };

    bool tryOverFlag = false, tryUnderFlag = false, tryApproxFlag = false;
    int underApproximation = 0, overApproximation = 0;
    std::string filename;

    Config config;

    int opt = 0;

    int long_index = 0;
    while ((opt = getopt_long(argc, argv,"o:u:OUAr:ni:m:ldv:cfbg", long_options, &long_index )) != -1) {
	switch (opt) {
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
	case 'A':
	    tryApproxFlag = true;
	    break;
	case 'p':
	    config.propagateUnconstrained = true;
	    break;
	case 'd':
	    config.useDontCares = true;
	    break;
	case 'c':
	    config.checkModels = true;
	    break;
	case 'f':
	    config.flipUniversalQuantifier = true;
	    break;
	case 'b':
	    config.propagateNecessaryBits = true;
	    break;
        case 'g':
	    config.goalUnconstrained = true;
	    break;
	case 'r':
	{
	    string optionString(optarg);

	    if (optionString == "win2")
	    {
		config.reorderType = WIN2;
	    }
	    else if (optionString == "win2ite")
	    {
		config.reorderType = WIN2_ITE;
	    }
	    else if (optionString == "win3")
	    {
		config.reorderType = WIN3;
	    }
	    else if (optionString == "win3ite")
	    {
		config.reorderType = WIN3_ITE;
	    }
	    else if (optionString == "sift")
	    {
		config.reorderType = SIFT;
	    }
	    else if (optionString == "siftite")
	    {
		config.reorderType = SIFT_ITE;
	    }
	    else if (optionString == "none")
	    {
		config.reorderType = NO_REORDER;
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
		config.initialOrder = HEURISTIC;
	    }
	    else if (optionString == "sequential")
	    {
		config.initialOrder = SEQUENTIAL;
	    }
	    else if (optionString == "interleave")
	    {
		config.initialOrder = INTERLEAVE_ALL;
	    }
	    else
	    {
		std::cout << "Invalid initial order type" << std::endl;
		exit(1);
	    }
	    break;
	}
	case 'm':
	{
	    string optionString(optarg);

	    if (optionString == "variables")
	    {
		config.approximationMethod = VARIABLES;
	    }
	    else if (optionString == "operations")
	    {
		config.approximationMethod = OPERATIONS;
	    }
	    else if (optionString == "both")
	    {
		config.approximationMethod = BOTH;
	    }
	    else
	    {
		std::cout << "Invalid approximation method" << std::endl;
		exit(1);
	    }
	    break;
	}
	case 'v':
	{
	    Logger::SetVerbosity(atoi(optarg));
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
	filename = std::string(argv[optind]);
    }
    else
    {
	std::cout << "Filename required" << std::endl;
	return 1;
    }

    Solver solver(config);
    Result result;

    z3::context ctx;
    Z3_ast ast = Z3_parse_smtlib2_file(ctx, filename.c_str(), 0, 0, 0, 0, 0, 0);
    z3::expr expr = to_expr(ctx, ast);

    if (overApproximation != 0)
    {
	result = solver.Solve(expr, OVERAPPROXIMATION, overApproximation);
    }
    else if (underApproximation != 0)
    {
	result = solver.Solve(expr, UNDERAPPROXIMATION, underApproximation);
    }
    else if (tryOverFlag)
    {
	result = solver.Solve(expr, OVERAPPROXIMATION);
    }
    else if (tryUnderFlag)
    {
	result = solver.Solve(expr, UNDERAPPROXIMATION);
    }
    else if (tryApproxFlag)
    {
	result = solver.SolveParallel(expr);
    }
    else
    {
	result = solver.Solve(expr);
    }

    cout << (result == SAT ? "sat" : result == UNSAT ? "unsat" : "unknown") << endl;
    exit(0);

    return 0;
}
