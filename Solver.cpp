#include "Solver.h"
#include "ExprSimplifier.h"

void bdd_error_handler(int errcode)
{
    std::cout << "BDD error: " << bdd_errstring(errcode) << std::endl;
    std::cout << "unknown" << std::endl;
    exit(0);
}

void Solver::set_bdd()
{
    if (bdd_isrunning())
    {
        bdd_done();
    }

    bdd_init(400000,100000);
    bdd_gbc_hook(NULL);
    bdd_error_hook(NULL);
}

Result Solver::GetResult(z3::expr expr)
{
    ExprSimplifier simplifier(expr.ctx(), m_propagateUncoinstrained);
    expr = simplifier.Simplify(expr);

    if (expr.is_const())
    {
        std::stringstream ss;
        if (ss.str() == "true")
        {
            //std::cout << "Reason: simplification" << std::endl;
            return SAT;
        }
        else if (ss.str() == "false")
        {
            //std::cout << "Reason: simplification" << std::endl;
            return UNSAT;
        }
    }

    if (expr.is_app())
    {
        auto decl = expr.decl();
        if (decl.name().str() == "or")
        {
            int numArgs = expr.num_args();
            for (int i = 0; i < numArgs; i++)
            {
                Result disjunctResult = GetResult(expr.arg(i));
                if (disjunctResult == SAT)
                {
                    return SAT;
                }
            }

            return UNSAT;
        }
    }

    set_bdd();

    ExprToBDDTransformer transformer(expr.ctx(), expr, m_initialOrder);
    transformer.setReorderType(m_reorderType);
    transformer.SetNegateMul(m_negateMul);

    if ((m_approximationType == OVERAPPROXIMATION || m_approximationType == UNDERAPPROXIMATION) && m_effectiveBitWidth == 0)
    {
        if (m_approximationType == OVERAPPROXIMATION)
        {
            return runWithOverApproximations(transformer);
        }
        else
        {
            return runWithUnderApproximations(transformer);
        }
    }

    if (m_approximationType == OVERAPPROXIMATION || m_approximationType == UNDERAPPROXIMATION)
    {
        if (m_approximationType == OVERAPPROXIMATION)
        {
            return runOverApproximation(transformer, m_effectiveBitWidth);
        }
        else
        {
            return runUnderApproximation(transformer, m_effectiveBitWidth);
        }
    }

    bdd returned = transformer.Proccess();

    // z3::solver s = z3::tactic(expr.ctx(), "bv").mk_solver();

    // s.add(expr);
// //    if (runZ3)
// //    {
//     auto z3result = s.check();
// //    }

    auto solverResult = returned.id() == 0 ? UNSAT : SAT;

//     if (solverResult == SAT && z3result == z3::check_result::unsat ||
// 	solverResult == UNSAT && z3result == z3::check_result::sat)
//     {
// 	abort();
//     }

    return solverResult;
}

Result Solver::runOverApproximation(ExprToBDDTransformer &transformer, int bitWidth)
{
    transformer.setApproximationType(SIGN_EXTEND);

    bdd returned = transformer.ProcessOverapproximation(bitWidth);
    return (returned.id() == 0 ? UNSAT : SAT);
}

Result Solver::runUnderApproximation(ExprToBDDTransformer &transformer, int bitWidth)
{
    transformer.setApproximationType(ZERO_EXTEND);

    bdd returned = transformer.ProcessUnderapproximation(bitWidth);
    return (returned.id() == 0 ? UNSAT : SAT);
}


Result Solver::runWithUnderApproximations(ExprToBDDTransformer &transformer)
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    int i = 1;

    Result underApproxResult = runUnderApproximation(transformer, i);
    if (underApproxResult == SAT)
    {
        std::cout << "Reason: underapproximation " << i << std::endl;
        return SAT;
    }

    underApproxResult = runUnderApproximation(transformer, -i);
    if (underApproxResult == SAT)
    {
        std::cout << "Reason: underapproximation " << -i << std::endl;
        return SAT;
    }

    for (int i = 2; i < 32; i = i+2)
    {
        Result underApproxResult = runUnderApproximation(transformer, i);
        if (underApproxResult == SAT)
        {
            std::cout << "Reason: underapproximation " << i << std::endl;
            return SAT;
        }

        std::cout << "underapproximation " << i << std::endl;
        underApproxResult = runUnderApproximation(transformer, -i);
        if (underApproxResult == SAT)
        {
            std::cout << "Reason: underapproximation " << -i << std::endl;
            return SAT;
        }
    }

    std::cout << "-------------------------" << std::endl;
    return UNKNOWN;
}

Result Solver::runWithOverApproximations(ExprToBDDTransformer &transformer)
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    int i = 1;

    Result overApproxResult = runOverApproximation(transformer, i);
    if (overApproxResult == UNSAT)
    {
        std::cout << "Reason: overapproximation " << i << std::endl;
        return UNSAT;
    }

    overApproxResult = runOverApproximation(transformer, -i);
    if (overApproxResult == UNSAT)
    {
        std::cout << "Reason: overapproximation " << -i << std::endl;
        return UNSAT;
    }

    for (i = 2; i < 32; i = i+2)
    {
        Result overApproxResult = runOverApproximation(transformer, i);
        if (overApproxResult == UNSAT)
        {
            std::cout << "Reason: overapproximation " << i << std::endl;
            return UNSAT;
        }

        overApproxResult = runOverApproximation(transformer, -i);
        if (overApproxResult == UNSAT)
        {
            std::cout << "Reason: overapproximation " << -i << std::endl;
            return UNSAT;
        }
    }

    std::cout << "-------------------------" << std::endl;
    return UNKNOWN;
}
