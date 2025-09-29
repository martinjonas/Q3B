#define CATCH_CONFIG_MAIN // This tells Catch to provide a main() - only do this
                          // in one cpp file
#include "../lib/Solver.h"
#include "catch.hpp"

#include "../lib/SMTLIBInterpreter.h"

#include "SMTLIBv2Lexer.h"
#include "SMTLIBv2Parser.h"
#include "antlr4-runtime.h"

using namespace antlr4;

Model model;

Result SolveWithoutApprox(std::string filename)
{
    std::cout << "Without approx: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = VARIABLES;
    config.approximations = NO_APPROXIMATIONS;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext *tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    auto result = interpreter.Run(tree->script());
    if (result == SAT) {
        model = interpreter.GetModel();
    }
    return result;
}

Result SolveWithVariableApprox(std::string filename,
                               Approximation approx = NO_APPROXIMATION)
{
    std::cout << "Var approx: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = VARIABLES;
    config.checkModels = false;
    if (approx == UNDERAPPROXIMATION)
        config.approximations = ONLY_UNDERAPPROXIMATIONS;
    else
        config.approximations = ONLY_OVERAPPROXIMATIONS;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext *tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}

Result SolveWithOperationsLimitApprox(std::string filename,
                                      Approximation approx = NO_APPROXIMATION,
                                      int precision = 0)
{
    std::cout << "Op approx: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = OPERATIONS;
    config.checkModels = true;
    if (approx == UNDERAPPROXIMATION)
        config.approximations = ONLY_UNDERAPPROXIMATIONS;
    else
        config.approximations = ONLY_OVERAPPROXIMATIONS;
    config.precision = precision;

    z3::context ctx;
    z3::solver s(ctx);
    s.from_file(filename.c_str());
    z3::expr expr = mk_and(s.assertions());

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext *tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}

Result SolveWithBothLimitApprox(std::string filename,
                                Approximation approx = NO_APPROXIMATION,
                                int precision = 0)
{
    std::cout << "Both approx: " << filename << std::endl;
    Config config;
    config.propagateUnconstrained = true;
    config.approximationMethod = BOTH;
    config.checkModels = true;
    if (approx == UNDERAPPROXIMATION)
        config.approximations = ONLY_UNDERAPPROXIMATIONS;
    else
        config.approximations = ONLY_OVERAPPROXIMATIONS;
    config.precision = precision;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext *tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);
    return interpreter.Run(tree->script());
}

Result SolveWithoutApproxAndGoalUnconstrained(std::string filename)
{
    Config config;
    config.propagateUnconstrained = true;
    config.goalUnconstrained = true;
    config.approximations = NO_APPROXIMATIONS;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext *tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}

Result SolveParallelAndGoalUnconstrained(std::string filename)
{
    Config config;
    config.propagateUnconstrained = true;
    config.goalUnconstrained = true;
    config.approximations = ALL_APPROXIMATIONS;

    std::ifstream stream;
    stream.open(filename);

    ANTLRInputStream input(stream);
    SMTLIBv2Lexer lexer(&input);
    CommonTokenStream tokens(&lexer);
    SMTLIBv2Parser parser{&tokens};

    SMTLIBv2Parser::StartContext *tree = parser.start();

    SMTLIBInterpreter interpreter;
    interpreter.SetConfig(config);

    return interpreter.Run(tree->script());
}

TEST_CASE("Without approximations", "[noapprox]")
{
    REQUIRE(SolveWithoutApprox("../tests/data/AR-fixpoint-1.smt2") == UNSAT);
    REQUIRE(SolveWithoutApprox(
                "../tests/data/cache-coherence-2-fixpoint-1.smt2") == UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/itc-b13-fixpoint-3.smt2") == SAT);
    REQUIRE(SolveWithoutApprox(
                "../tests/data/"
                "Fibonacci01_true-unreach-call_true-no-overflow.c_905.smt2") ==
            SAT);
    REQUIRE(SolveWithoutApprox("../tests/data/nlzbe008.smt2") == UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/falseAndFalse.smt2") == UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/bvshl0.smt2") == SAT);
    REQUIRE(SolveWithoutApprox(
                "../tests/data/check_bvsge_bvashr0_16bit.smt2") == UNSAT);
    REQUIRE(SolveWithoutApprox(
                "../tests/data/magnetic_field-node118398.smt2") == UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/unconstrainedMulVar.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/check_bvsle_bvmul_8bit.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/unconstrainedMulConst.smt2") ==
            SAT);
    REQUIRE(SolveWithoutApprox(
                "../tests/data/check_eq_bvconcat0_2_64bit.smt2") == UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/002.smt2") == UNSAT);
    REQUIRE(
        SolveWithoutApprox(
            "../tests/data/MADWiFi-encode_ie_ok_true-unreach-call.i_7.smt2") ==
        UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/usb-phy-fixpoint-1.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/pi-bus-fixpoint-1.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/check_eq_bvshl0_32bit.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox(
                "../tests/data/check_bvuge_bvashr1_64bit.smt2") == UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/preiner_bug_2020.smt2") == UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/smtcomp23/heapsort.i_0.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/smtcomp23/heapsort.i_3.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/smtcomp23/heapsort.i_8.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/smtcomp23/heapsort.i_9.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox("../tests/data/smtcomp23/minimal.smt2") ==
            UNSAT);
    REQUIRE(SolveWithoutApprox(
                "../tests/data/"
                "btor2c-eagerMod.bakery.1.prop1-func-interl.c_0.smt2") == SAT);
}

TEST_CASE("With variable approximations", "[variableapprox]")
{
    REQUIRE(SolveWithVariableApprox(
                "../tests/data/audio_ac97_wavepcistream2.cpp.smt2",
                OVERAPPROXIMATION) == UNSAT);
    REQUIRE(
        SolveWithVariableApprox(
            "../tests/data/jain_7_true-unreach-call_true-no-overflow.i_61.smt2",
            OVERAPPROXIMATION) == UNSAT);
    REQUIRE(SolveWithVariableApprox("../tests/data/RNDPRE_3_48.smt2",
                                    UNDERAPPROXIMATION) == SAT);
    REQUIRE(
        SolveWithVariableApprox("../tests/data/ETCS-essentials-node3023.smt2",
                                UNDERAPPROXIMATION) == SAT);
    REQUIRE(SolveWithVariableApprox("../tests/data/accelerating-node2100.smt2",
                                    UNDERAPPROXIMATION) == SAT);
    REQUIRE(SolveWithVariableApprox(
                "../tests/data/binary_driver-2007-10-09-node11383.smt2",
                UNDERAPPROXIMATION) == SAT);
    REQUIRE(SolveWithVariableApprox("../tests/data/ARI118=1.smt2",
                                    OVERAPPROXIMATION) == UNSAT);
}

TEST_CASE("With bothLimit approximations", "[bothlimitapprox]")
{
    REQUIRE(SolveWithBothLimitApprox("../tests/data/RNDPRE_4_42.smt2",
                                     OVERAPPROXIMATION) == UNSAT);
    REQUIRE(SolveWithBothLimitApprox("../tests/data/RND_6_4.smt2",
                                     UNDERAPPROXIMATION) == SAT);
    REQUIRE(
        SolveWithBothLimitApprox(
            "../tests/data/jain_7_true-unreach-call_true-no-overflow.i_61.smt2",
            OVERAPPROXIMATION) == UNSAT);

    // correct model returned by an overapproximation
    REQUIRE(SolveWithBothLimitApprox("../tests/data/007.smt2",
                                     OVERAPPROXIMATION) == SAT);
    REQUIRE(
        SolveWithBothLimitApprox(
            "../tests/data/sum02_true-unreach-call_true-no-overflow.i_375.smt2",
            OVERAPPROXIMATION) == SAT);
    REQUIRE(
        SolveWithBothLimitApprox("../tests/data/check_bvsgt_bvudiv1_8bit.smt2",
                                 UNDERAPPROXIMATION) != SAT);
    REQUIRE(SolveWithBothLimitApprox("../tests/data/bvurem_approx.smt2",
                                     UNDERAPPROXIMATION, 1) != SAT);
    REQUIRE(SolveWithBothLimitApprox("../tests/data/RND_3_14.smt2") == UNSAT);
}

TEST_CASE("With bothLimit approximations -- term introducer ",
          "[bothlimitapprox-ti]")
{
    REQUIRE(
        SolveWithBothLimitApprox(
            "../tests/data/intersection-example-onelane.proof-node1469.smt2",
            OVERAPPROXIMATION) == UNSAT);
}

TEST_CASE("With operation approximations -- ite ", "[opapproxlimit-ite]")
{
    REQUIRE(SolveWithOperationsLimitApprox("../tests/data/iteApprox.smt2",
                                           UNDERAPPROXIMATION, 1) != UNSAT);
}

TEST_CASE("With parallel approximations", "[parallel]")
{
    REQUIRE(SolveParallelAndGoalUnconstrained("../tests/data/003.smt2") == SAT);
}

TEST_CASE("SMT-COMP 2018", "[smtcomp18]")
{
    REQUIRE(SolveWithVariableApprox("../tests/data/smtcomp18/01.smt2",
                                    UNDERAPPROXIMATION) != SAT);
    REQUIRE(SolveWithBothLimitApprox("../tests/data/smtcomp18/02.smt2",
                                     OVERAPPROXIMATION, 1) != UNSAT);
}

TEST_CASE("Without approximations -- goal unconstrained", "[goalunconstrained]")
{
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/check_bvuge_bvudiv0_4bit.smt2") != SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/check_bvugt_bvshl0_4bit.smt2") != SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/check_bvsle_bvlshr0_4bit.smt2") != SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/check_bvsle_bvashr0_4bit.smt2") != SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/check_bvslt_bvashr0_4bit.smt2") != SAT);
}

TEST_CASE("SMT-LIB", "[smtlib]")
{
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/smtlib/binaryNumeral.smt2") == SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/smtlib/hexNumeral.smt2") == SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/smtlib/push.smt2") == SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/smtlib/pushPush.smt2") == UNSAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/smtlib/pushPushPop.smt2") == SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/smtlib/push2Pop.smt2") == UNSAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/smtlib/push2Pop2.smt2") == SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/smtlib/reset.smt2") == SAT);
    REQUIRE(SolveWithoutApproxAndGoalUnconstrained(
                "../tests/data/smtlib/resetAssertions.smt2") == SAT);
}

TEST_CASE("Models", "[models]")
{
    REQUIRE(SolveWithoutApprox("../tests/data/smtlib/model1.smt2") == SAT);
    REQUIRE(model.find("x") != model.end());
    REQUIRE(std::get<1>(model["x"]) ==
            std::vector<bool>{false, false, false, true});

    REQUIRE(SolveWithoutApprox("../tests/data/smtlib/model2.smt2") == SAT);
    REQUIRE(model.find("x") != model.end());
    REQUIRE(model.find("y") != model.end());
    REQUIRE(model.find("z") != model.end());
    REQUIRE(std::get<1>(model["x"]) ==
            std::vector<bool>{false, false, false, true});
    REQUIRE(std::get<1>(model["y"]) ==
            std::vector<bool>{false, false, false, true});
    REQUIRE(std::get<1>(model["z"]) ==
            std::vector<bool>{false, false, true, false});

    REQUIRE(SolveWithoutApprox("../tests/data/smtlib/model3.smt2") == SAT);
    REQUIRE(model.find("x") != model.end());
    REQUIRE(model.find("y") != model.end());
    REQUIRE(model.find("z") != model.end());
    REQUIRE(std::get<1>(model["x"]) ==
            std::vector<bool>{false, false, true, true});
    REQUIRE(std::get<1>(model["y"]) ==
            std::vector<bool>{false, false, true, true});
    REQUIRE(std::get<1>(model["z"]) ==
            std::vector<bool>{true, false, false, true});
}
