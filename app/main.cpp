#include <fstream>
#include <getopt.h>
#include <iostream>
#include <string>
#include <z3++.h>

#include "../lib/Config.h"
#include "../lib/Logger.h"
#include "../lib/SMTLIBInterpreter.h"
#include "../lib/Solver.h"

#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"
#include "antlr4-runtime.h"

using namespace std;
using namespace z3;
using namespace antlr4;

const std::string version = "1.1";

void print_usage()
{
    std::cout << "Q3B (version " << version << ")" << std::endl;
    std::cout << "Usage: q3b [options] file.smt2" << std::endl << std::endl;

    std::cout << "Supported options without parameters:" << std::endl;
    std::cout << "  --help                      print this help" << std::endl;
    std::cout << "  --version                   print version" << std::endl
              << std::endl;

    std::cout << "Supported options with parameters [--option=value]:"
              << std::endl;
    std::cout << "  --abstractions              use abstractions "
                 "(none|under|over|all) [all]"
              << std::endl;
    std::cout << "  --abstract:methods          type of abstractions "
                 "(variables|operations|both) [both]"
              << std::endl;
    std::cout << "  --abstract:check-models     check models produces by "
                 "overapproximation [1]"
              << std::endl;
    std::cout << "  --abstract:necessary-bits   deduce forced values of bits "
                 "from overapproximation [1]"
              << std::endl;
    std::cout << "  --simpl:add-congruences     add congruences for expensive "
                 "operations [1]"
              << std::endl;
    std::cout << "  --simpl:unconstrained       use unconstrained variable "
                 "simplification [1]"
              << std::endl;
    std::cout << "  --uc:goal                   take goals of unconstrained "
                 "variables into account [1]"
              << std::endl;
    std::cout << "  --bdd:reorder               BDD reorder type "
                 "(none|win2|win2ite|win3|win3ite|sift|siftite) [sift]"
              << std::endl;
    std::cout << "  --simpl:flip-universal      negate universal formulas [0]"
              << std::endl;
    std::cout
        << "  --verbosity                 set level of debugging outputs [0]"
        << std::endl;
}

int main(int argc, char *argv[])
{
    static struct option long_options[] = {
        {"abstractions", required_argument, 0, 'a'},
        {"abstract:method", required_argument, 0, 'm'},
        {"abstract:check-models", required_argument, 0, 'c'},
        {"abstract:necessary-bits", required_argument, 0, 'b'},
        {"simpl:unconstrained", required_argument, 0, 'p'},
        {"simpl:add-congruences", required_argument, 0, 'C'},
        {"uc:goal", required_argument, 0, 'g'},
        {"bdd:reorder", required_argument, 0, 'r'},
        {"simpl:flip-universal", required_argument, 0, 'f'},
        {"verbosity", required_argument, 0, 'v'},
        {"version", no_argument, 0, 'V'},
        {"help", no_argument, 0, 'h'},
        {0, 0, 0, 0}};

    std::string filename;
    Config config;

    int opt = 0;
    int long_index = 0;
    while ((opt = getopt_long(argc, argv, "a:m:b:p:g:r:i:c:C:f:v:hV",
                              long_options, &long_index)) != -1) {
        switch (opt) {
        case 'a': {
            string optionString(optarg);

            config.approximations = NO_APPROXIMATIONS;
            if (optionString == "over")
                config.approximations = ONLY_OVERAPPROXIMATIONS;
            else if (optionString == "under")
                config.approximations = ONLY_UNDERAPPROXIMATIONS;
            else if (optionString == "all")
                config.approximations = ALL_APPROXIMATIONS;
            break;
        }
        case 'p':
            config.propagateUnconstrained = atoi(optarg);
            break;
        case 'c':
            config.checkModels = atoi(optarg);
            break;
        case 'C':
            config.addCongruences = atoi(optarg);
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
        case 'r': {
            string optionString(optarg);

            if (optionString == "win2")
                config.reorderType = WIN2;
            else if (optionString == "win2ite")
                config.reorderType = WIN2_ITE;
            else if (optionString == "win3")
                config.reorderType = WIN3;
            else if (optionString == "win3ite")
                config.reorderType = WIN3_ITE;
            else if (optionString == "sift")
                config.reorderType = SIFT;
            else if (optionString == "siftite")
                config.reorderType = SIFT_ITE;
            else if (optionString == "none")
                config.reorderType = NO_REORDER;
            else {
                std::cout << "Invalid reorder type" << std::endl;
                print_usage();
                exit(1);
            }

            break;
        }
        case 'm': {
            string optionString(optarg);

            if (optionString == "variables")
                config.approximationMethod = VARIABLES;
            else if (optionString == "operations")
                config.approximationMethod = OPERATIONS;
            else if (optionString == "both")
                config.approximationMethod = BOTH;
            else {
                std::cout << "Invalid abstraction method" << std::endl;
                print_usage();
                exit(1);
            }
            break;
        }
        case 'v': {
            Logger::SetVerbosity(atoi(optarg));
            break;
        }
        case 'V': {
            std::cout << "Q3B version " << version << std::endl;
            return 0;
        }
        case 'h': {
            print_usage();
            return 0;
        }

        default:
            std::cout << "Invalid arguments" << std::endl << std::endl;
            print_usage();
            return 1;
        }
    }

    if (optind < argc) {
        filename = std::string(argv[optind]);
    } else {
        std::cout << "Filename required" << std::endl;
        print_usage();
        return 1;
    }

    Solver solver(config);

    std::ifstream stream;
    stream.open(filename);
    if (!stream.good()) {
        std::cout << "(error \"failed to open file '" << filename << "'\")"
                  << std::endl;
        return 1;
    }

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser(&tokens);

    SMTLIBv2Parser::StartContext *tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);
    interpreter.Run(tree->script());
}
