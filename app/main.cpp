#include <iostream>
#include <string>
#include <z3++.h>
#include <fstream>
#include <getopt.h>

#include "../lib/Solver.h"
#include "../lib/Logger.h"
#include "../lib/Config.h"

using namespace std;
using namespace z3;

const std::string version = "0.9 dev";

void print_usage()
{
    std::cout << "Q3B (version " << version << ")" << std::endl;
    std::cout << "Usage: q3b [options] file.smt2" << std::endl << std::endl;

    std::cout << "Supported options without parameters:" << std::endl;
    std::cout << "  --help                      print this help" << std::endl;
    std::cout << "  --version                   print version" << std::endl << std::endl;

    std::cout << "Supported options with parameters [--option=value]:" << std::endl;
    std::cout << "  --abstractions              use abstractions (none|under|over|all) [all]" << std::endl;
    std::cout << "  --abstract:methods          type of abstractions (variables|operations|both) [both]" << std::endl;
    std::cout << "  --abstract:check-models     check models produces by overapproximation [1]" << std::endl;
    std::cout << "  --abstract:necessary-bits   deduce forced values of bits from overapproximation [1]" << std::endl;
    std::cout << "  --simpl:unconstrained       use unconstrained variable simplification [1]" << std::endl;
    std::cout << "  --uc:goal                   take goals of unconstrained variables into account [1]" << std::endl;
    std::cout << "  --bdd:reorder               BDD reorder type (none|win2|win2ite|win3|win3ite|sift|siftite) [sift]" << std::endl;
    std::cout << "  --bdd:initial-order         initial order of BDD variables (interleave|sequential|heuristic) [heuristic]" << std::endl;
    std::cout << "  --simpl:flip-universal      negate universal formulas [0]" << std::endl;
    std::cout << "  --verbosity                 set level of debugging outputs [0]" << std::endl;
}


int main(int argc, char* argv[])
{
    static struct option long_options[] = {
	{"abstractions", required_argument, 0, 'a' },
	{"abstract:method", required_argument, 0, 'm' },
        {"abstract:check-models", required_argument, 0, 'c' },
	{"abstract:necessary-bits", required_argument, 0, 'b' },
        {"simpl:unconstrained", required_argument, 0, 'p' },
        {"uc:goal", required_argument, 0, 'g' },
	{"bdd:reorder", required_argument, 0, 'r' },
	{"bdd:initial-order", required_argument, 0, 'i' },
	{"simpl:flip-universal", required_argument, 0, 'f' },
	{"verbosity", required_argument, 0, 'v' },
        {"version", no_argument, 0, 'V' },
        {"help", no_argument, 0, 'h' },
	{0,           0,                 0,  0   }
    };

    bool tryOverFlag = false, tryUnderFlag = false, tryApproxFlag = true;
    std::string filename;
    Config config;

    int opt = 0;
    int long_index = 0;
    while ((opt = getopt_long(argc, argv,"a:m:b:p:g:r:i:c:f:v:hV", long_options, &long_index )) != -1) {
	switch (opt) {
	case 'a':
        {
            string optionString(optarg);

            tryApproxFlag = false;
            if (optionString == "over") tryOverFlag = true;
            else if (optionString == "under") tryUnderFlag = true;
            else if (optionString == "all") tryApproxFlag = true;
	    break;
        }
	case 'p':
	    config.propagateUnconstrained = atoi(optarg);
	    break;
	case 'c':
	    config.checkModels = atoi(optarg);
	    break;
	case 'f':
	    config.flipUniversalQuantifier = atoi(optarg);
	    break;
	case 'b':
	    config.propagateNecessaryBits = atoi(optarg);
	    break;
        case 'g':
	    config.goalUnconstrained = atoi(optarg);
	    break;
	case 'r':
	{
	    string optionString(optarg);

	    if (optionString == "win2") config.reorderType = WIN2;
	    else if (optionString == "win2ite") config.reorderType = WIN2_ITE;
	    else if (optionString == "win3") config.reorderType = WIN3;
	    else if (optionString == "win3ite") config.reorderType = WIN3_ITE;
	    else if (optionString == "sift") config.reorderType = SIFT;
	    else if (optionString == "siftite")	config.reorderType = SIFT_ITE;
	    else if (optionString == "none") config.reorderType = NO_REORDER;
	    else
	    {
		std::cout << "Invalid reorder type" << std::endl;
                print_usage();
		exit(1);
	    }

	    break;
	}
	case 'i':
	{
	    string optionString(optarg);

	    if (optionString == "heuristic") config.initialOrder = HEURISTIC;
	    else if (optionString == "sequential") config.initialOrder = SEQUENTIAL;
	    else if (optionString == "interleave") config.initialOrder = INTERLEAVE_ALL;
	    else
	    {
		std::cout << "Invalid initial order type" << std::endl;
                print_usage();
		exit(1);
	    }
	    break;
	}
	case 'm':
	{
	    string optionString(optarg);

	    if (optionString == "variables") config.approximationMethod = VARIABLES;
	    else if (optionString == "operations") config.approximationMethod = OPERATIONS;
	    else if (optionString == "both") config.approximationMethod = BOTH;
	    else
	    {
		std::cout << "Invalid abstraction method" << std::endl;
                print_usage();
		exit(1);
	    }
	    break;
	}
	case 'v':
	{
	    Logger::SetVerbosity(atoi(optarg));
	    break;
	}
	case 'V':
	{
            std::cout << "Q3B version " << version << std::endl;
            return 0;
	}
	case 'h':
	{
            print_usage();
            return 0;
	}

	default:
	    std::cout << "Invalid arguments" << std::endl << std::endl;
            print_usage();
	    return 1;
	}
    }

    if (optind < argc)
    {
	filename = std::string(argv[optind]);
    }
    else
    {
	std::cout << "Filename required" << std::endl;
        print_usage();
	return 1;
    }

    Solver solver(config);
    Result result;

    z3::context ctx;
    Z3_ast ast = Z3_parse_smtlib2_file(ctx, filename.c_str(), 0, 0, 0, 0, 0, 0);
    z3::expr expr = to_expr(ctx, ast);

    if (tryOverFlag) result = solver.Solve(expr, OVERAPPROXIMATION);
    else if (tryUnderFlag) result = solver.Solve(expr, UNDERAPPROXIMATION);
    else if (tryApproxFlag) result = solver.SolveParallel(expr);
    else result = solver.Solve(expr);

    cout << (result == SAT ? "sat" : result == UNSAT ? "unsat" : "unknown") << endl;
    exit(0); //return 0 would cause memory cleanup issues in the Z3 context
}
