#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch.hpp"
#include "../lib/Solver.cpp"

Result SolveWithoutApprox(std::string filename)
{
    Solver solver(true);
    solver.SetInitialOrder(HEURISTIC);
    solver.SetNegateMul(false);
    solver.SetReorderType(NO_REORDER);
    //solver.SetApproximationMethod(approximationMethod);
    solver.SetLimitBddSizes(false);
    solver.SetUseDontCares(false);

    z3::context ctx;
    Z3_ast ast = Z3_parse_smtlib2_file(ctx, filename.c_str(), 0, 0, 0, 0, 0, 0);
    z3::expr expr = to_expr(ctx, ast);

    return solver.Solve(expr);
}

Result SolveWithVariableApprox(std::string filename, Approximation approx = NO_APPROXIMATION)
{
    Solver solver(true);
    solver.SetInitialOrder(HEURISTIC);
    solver.SetNegateMul(false);
    solver.SetReorderType(NO_REORDER);
    solver.SetApproximationMethod(VARIABLES);
    solver.SetLimitBddSizes(false);
    solver.SetUseDontCares(false);

    z3::context ctx;
    Z3_ast ast = Z3_parse_smtlib2_file(ctx, filename.c_str(), 0, 0, 0, 0, 0, 0);
    z3::expr expr = to_expr(ctx, ast);

    return solver.Solve(expr, approx);
}

Result SolveWithBothLimitApprox(std::string filename, Approximation approx = NO_APPROXIMATION)
{
    Solver solver(true);
    solver.SetInitialOrder(HEURISTIC);
    solver.SetNegateMul(false);
    solver.SetReorderType(NO_REORDER);
    solver.SetApproximationMethod(BOTH);
    solver.SetLimitBddSizes(true);
    solver.SetUseDontCares(false);

    z3::context ctx;
    Z3_ast ast = Z3_parse_smtlib2_file(ctx, filename.c_str(), 0, 0, 0, 0, 0, 0);
    z3::expr expr = to_expr(ctx, ast);

    return solver.Solve(expr, approx);
}

TEST_CASE( "Without approximations", "[noapprox]" )
{
    REQUIRE( SolveWithoutApprox("../tests/data/AR-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/cache-coherence-2-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/itc-b13-fixpoint-3.smt2") == SAT );
    REQUIRE( SolveWithoutApprox("../tests/data/Fibonacci01_true-unreach-call_true-no-overflow.c_905.smt2") == SAT );
}

TEST_CASE( "With variable approximations", "[variableapprox]" )
{
    REQUIRE( SolveWithVariableApprox("../tests/data/audio_ac97_wavepcistream2.cpp.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithVariableApprox("../tests/data/RNDPRE_3_48.smt2", UNDERAPPROXIMATION) == SAT );
}

TEST_CASE( "With bothLimit approximations", "[bothlimitapprox]" )
{
    REQUIRE( SolveWithBothLimitApprox("../tests/data/RNDPRE_4_42.smt2", OVERAPPROXIMATION) == UNSAT );
    REQUIRE( SolveWithBothLimitApprox("../tests/data/RND_6_4.smt2", UNDERAPPROXIMATION) == SAT );
}
