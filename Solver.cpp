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
            return runOverApproximation(transformer, m_effectiveBitWidth, abs(m_effectiveBitWidth));
        }
        else
        {
            return runUnderApproximation(transformer, m_effectiveBitWidth, abs(m_effectiveBitWidth));
        }
    }

    BDD returned = transformer.Proccess();
    return returned.IsZero() ? UNSAT : SAT;
}

Result Solver::runOverApproximation(ExprToBDDTransformer &transformer, int bitWidth, unsigned int precision)
{
    transformer.setApproximationType(SIGN_EXTEND);

    BDD returned = transformer.ProcessOverapproximation(bitWidth, precision);
    return returned.IsZero() ? UNSAT : SAT;
}

Result Solver::runUnderApproximation(ExprToBDDTransformer &transformer, int bitWidth, unsigned int precision)
{
    transformer.setApproximationType(ZERO_EXTEND);

    BDD returned = transformer.ProcessUnderapproximation(bitWidth, precision);
    return returned.IsZero() ? UNSAT : SAT;
}

Result Solver::runWithApproximations(ExprToBDDTransformer &transformer, Approximation approximation)
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    if (approximation == NO_APPROXIMATION)
    {
	std::cout << "Invalid approximation" << std::endl;
	exit(1);
    }

    Result reliableResult = approximation == UNDERAPPROXIMATION ? SAT : UNSAT;
    auto runFunction = [this, &approximation](auto &transformer, int bitWidth, unsigned int precision){
	if (approximation == UNDERAPPROXIMATION)
	{
	    return runUnderApproximation(transformer, bitWidth, precision);
	}
	else
	{
	    return runOverApproximation(transformer, bitWidth, precision);
	}
    };

    auto approx = [this, &runFunction, &transformer, &reliableResult](int bw, unsigned int prec)
    {
	Result approxResult = runFunction(transformer, bw, prec);

	if (approxResult == reliableResult || transformer.IsPreciseResult())
	{
	    return approxResult;
	}

	if (m_approximationMethod == VARIABLES || m_approximationMethod == BOTH)
	{
	    approxResult = runFunction(transformer, -bw, prec);

	    if (approxResult == reliableResult)
	    {
		return approxResult;
	    }
	}

	return UNKNOWN;
    };

    for (unsigned int prec = 1; prec < 32; prec += 2)
    {
	Result approxResult = approx(1, prec);

	if (approxResult != UNKNOWN)
	{
	    return approxResult;
	}

	if (!transformer.OperationApproximationHappened())
	{
	    break;
	}
    }

    for (int i = 2; i < 32; i = i+2)
    {
	for (unsigned int prec = 1; prec < 32; prec += 2)
	{
	    Result approxResult = approx(i, prec);

	    approxResult = approx(i, i);
	    if (approxResult != UNKNOWN)
	    {
		return approxResult;
	    }
	}

	if (!transformer.OperationApproximationHappened())
	{
	    break;
	}
    }

    return UNKNOWN;
}



Result Solver::runWithUnderApproximations(ExprToBDDTransformer &transformer)
{
    return runWithApproximations(transformer, UNDERAPPROXIMATION);
}

Result Solver::runWithOverApproximations(ExprToBDDTransformer &transformer)
{
    return runWithApproximations(transformer, OVERAPPROXIMATION);
}
