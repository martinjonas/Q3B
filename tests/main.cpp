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
    auto expr = to_expr(ctx, ast);

    return solver.GetResult(expr);
}

TEST_CASE( "Without approximations", "[noapprox]" )
{
    REQUIRE( SolveWithoutApprox("../tests/data/AR-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/cache-coherence-2-fixpoint-1.smt2") == UNSAT );
    REQUIRE( SolveWithoutApprox("../tests/data/itc-b13-fixpoint-3.smt2") == SAT );
    REQUIRE( SolveWithoutApprox("../tests/data/Fibonacci01_true-unreach-call_true-no-overflow.c_905.smt2") == SAT );
}
