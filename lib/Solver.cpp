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
    if (m_useDontCares)
    {
	transformer.SetDontCare(!returned);
    }
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

    assert (approximation != NO_APPROXIMATION);

    Result reliableResult = approximation == UNDERAPPROXIMATION ? SAT : UNSAT;
    auto runFunction = [this, &approximation](auto &transformer, int bitWidth, unsigned int precision){
	return (approximation == UNDERAPPROXIMATION) ?
	   runUnderApproximation(transformer, bitWidth, precision) :
	   runOverApproximation(transformer, bitWidth, precision);
    };

    if (m_approximationMethod == BOTH)
    {
	unsigned int prec = 1;
	unsigned int lastBW = 1;
	while (prec != 0)
	{
	    std::cout << "Limit: " << prec << std::endl;
	    // std::cout << "BW: 0, ";

	    // transformer.setApproximationMethod(OPERATIONS);
	    // Result approxResult = runFunction(transformer, 0, prec);
	    // if (approxResult == reliableResult || transformer.IsPreciseResult())
	    // {
	    // 	std::cout << std::endl;
	    // 	return approxResult;
	    // }
	    // transformer.setApproximationMethod(BOTH);

	    if (lastBW == 1)
	    {
		std::cout << lastBW << std::flush;

		Result approxResult = runFunction(transformer, lastBW, prec);
		if (approxResult == reliableResult || transformer.IsPreciseResult())
		{
		    std::cout << std::endl;
		    return approxResult;
		}

		bool approxHappened = transformer.OperationApproximationHappened();

		approxResult = runFunction(transformer, -1, prec);
		if (approxResult == reliableResult || transformer.IsPreciseResult())
		{
		    std::cout << std::endl;
		    return approxResult;
		}

		if (approxHappened || transformer.OperationApproximationHappened())
		{
		    prec *= 2;
		    std::cout << std::endl;
		    continue;
		}

		lastBW++;
	    }

	    for (int bw = lastBW; bw <= 32; bw += 2)
	    {
		std::cout << ", " << bw << std::flush;
		Result approxResult = runFunction(transformer, bw, prec);
		if (approxResult == reliableResult || transformer.IsPreciseResult())
		{
		    std::cout << std::endl;
		    return approxResult;
		}

		bool approxHappened = transformer.OperationApproximationHappened();

		if (m_approximationMethod == VARIABLES || m_approximationMethod == BOTH)
		{
		    approxResult = runFunction(transformer, -bw, prec);
		    if (approxResult == reliableResult || transformer.IsPreciseResult())
		    {
			std::cout << std::endl;
			return approxResult;
		    }
		}

		if (approxHappened || transformer.OperationApproximationHappened())
		{
		    lastBW = bw;
		    break;
		}
	    }

	    std::cout << std::endl;
	    prec *= 2;
	}
    }
    else if (m_approximationMethod == VARIABLES)
    {
	Result approxResult = runFunction(transformer, 1, 0);
	if (approxResult == reliableResult || transformer.IsPreciseResult())
	{
	    return approxResult;
	}

	approxResult = runFunction(transformer, -1, 0);
	if (approxResult == reliableResult || transformer.IsPreciseResult())
	{
	    return approxResult;
	}

	for (int bw = 2; bw < 32; bw += 2)
	{
	    approxResult = runFunction(transformer, bw, 0);
	    if (approxResult == reliableResult || transformer.IsPreciseResult())
	    {
		return approxResult;
	    }

	    approxResult = runFunction(transformer, -bw, 0);
	    if (approxResult == reliableResult)
	    {
		return approxResult;
	    }
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
