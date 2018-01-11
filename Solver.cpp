#include "Solver.h"
#include "ExprSimplifier.h"

Result Solver::GetResult(z3::expr expr)
{
    ExprSimplifier simplifier(expr.ctx(), m_propagateUncoinstrained);
    expr = simplifier.Simplify(expr);

    if (expr.is_const())
    {
        std::stringstream ss;
	ss << expr;
        if (ss.str() == "true")
        {
            return SAT;
        }
        else if (ss.str() == "false")
        {
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
		if (GetResult(expr.arg(i)) == UNKNOWN)
		{
		    return UNKNOWN;
		}

                if (GetResult(expr.arg(i)) == SAT)
                {
                    return SAT;
                }
            }

            return UNSAT;
        }
    }

    ExprToBDDTransformer transformer(expr.ctx(), expr, m_initialOrder);
    transformer.setReorderType(m_reorderType);
    transformer.SetNegateMul(m_negateMul);
    transformer.setApproximationMethod(m_approximationMethod);
    transformer.SetLimitBddSizes(m_limitBddSizes);

    if (m_approximationType == OVERAPPROXIMATION || m_approximationType == UNDERAPPROXIMATION)
    {
	if (m_effectiveBitWidth == 0)
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

        if (m_approximationType == OVERAPPROXIMATION)
        {
            return runOverApproximation(transformer, m_effectiveBitWidth);
        }
        else
        {
            return runUnderApproximation(transformer, m_effectiveBitWidth);
        }
    }

    BDD returned = transformer.Proccess();
    return returned.IsZero() ? UNSAT : SAT;
}

Result Solver::runOverApproximation(ExprToBDDTransformer &transformer, int bitWidth)
{
    transformer.setApproximationType(SIGN_EXTEND);

    BDD returned = transformer.ProcessOverapproximation(bitWidth);
    return returned.IsZero() ? UNSAT : SAT;
}

Result Solver::runUnderApproximation(ExprToBDDTransformer &transformer, int bitWidth)
{
    transformer.setApproximationType(ZERO_EXTEND);

    BDD returned = transformer.ProcessUnderapproximation(bitWidth);
    return returned.IsZero() ? UNSAT : SAT;
}


Result Solver::runWithUnderApproximations(ExprToBDDTransformer &transformer)
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    int i = 1;

    Result underApproxResult = runUnderApproximation(transformer, i);
    if (underApproxResult == SAT)
    {
        return SAT;
    }
    else if (underApproxResult == UNSAT && transformer.IsPreciseResult())
    {
	return UNSAT;
    }

    if (m_approximationMethod == VARIABLES || m_approximationMethod == BOTH)
    {
	underApproxResult = runUnderApproximation(transformer, -i);
	if (underApproxResult == SAT)
	{
	    return SAT;
	}
	else if (underApproxResult == UNSAT && transformer.IsPreciseResult())
	{
	    return UNSAT;
	}
    }

    for (int i = 2; i < 32; i = i+2)
    {
        Result underApproxResult = runUnderApproximation(transformer, i);
        if (underApproxResult == SAT)
        {
            return SAT;
        }
	else if (underApproxResult == UNSAT && transformer.IsPreciseResult())
	{
	    return UNSAT;
	}

	if (m_approximationMethod == VARIABLES || m_approximationMethod == BOTH)
	{
	    underApproxResult = runUnderApproximation(transformer, -i);
	    if (underApproxResult == SAT)
	    {
		return SAT;
	    }
	    else if (underApproxResult == UNSAT && transformer.IsPreciseResult())
	    {
		return UNSAT;
	    }
	}
    }

    return UNKNOWN;
}

Result Solver::runWithOverApproximations(ExprToBDDTransformer &transformer)
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    int i = 1;

    Result overApproxResult = runOverApproximation(transformer, i);
    if (overApproxResult == UNSAT)
    {
        return UNSAT;
    }
    else if (overApproxResult == SAT && transformer.IsPreciseResult())
    {
	return SAT;
    }

    if (m_approximationMethod == VARIABLES || m_approximationMethod == BOTH)
    {
	overApproxResult = runOverApproximation(transformer, -i);
	if (overApproxResult == UNSAT)
	{
	    return UNSAT;
	}
	else if (overApproxResult == SAT && transformer.IsPreciseResult())
	{
	    return SAT;
	}
    }

    for (i = 2; i < 32; i = i+2)
    {
        Result overApproxResult = runOverApproximation(transformer, i);
        if (overApproxResult == UNSAT)
        {
            return UNSAT;
        }
	else if (overApproxResult == SAT && transformer.IsPreciseResult())
	{
	    return SAT;
	}

	if (m_approximationMethod == VARIABLES || m_approximationMethod == BOTH)
	{
	    overApproxResult = runOverApproximation(transformer, -i);
	    if (overApproxResult == UNSAT)
	    {
		return UNSAT;
	    }
	    else if (overApproxResult == SAT && transformer.IsPreciseResult())
	    {
		return SAT;
	    }
	}
    }

    return UNKNOWN;
}
