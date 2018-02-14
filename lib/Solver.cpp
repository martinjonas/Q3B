#include "Solver.h"
#include "ExprSimplifier.h"

#include <thread>
#include <functional>

std::mutex Solver::m;
std::mutex Solver::m_z3context;

Result Solver::getResult(z3::expr expr, Approximation approximation, unsigned int effectiveBitWidth)
{
    if (expr.is_const())
    {
	if (expr.is_app() && expr.decl().decl_kind() == Z3_OP_TRUE)
        {
            return SAT;
        }
	else if (expr.is_app() && expr.decl().decl_kind() == Z3_OP_FALSE)
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
		if (getResult(expr.arg(i), approximation, effectiveBitWidth) == UNKNOWN)
		{
		    return UNKNOWN;
		}

                if (getResult(expr.arg(i), approximation, effectiveBitWidth) == SAT)
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

    if (approximation == OVERAPPROXIMATION || approximation == UNDERAPPROXIMATION)
    {
	if (effectiveBitWidth == 0)
	{
	    if (approximation == OVERAPPROXIMATION)
	    {
		return runWithOverApproximations(transformer);
	    }
	    else
	    {
		return runWithUnderApproximations(transformer);
	    }
	}

        if (approximation == OVERAPPROXIMATION)
        {
            return runOverApproximation(transformer, effectiveBitWidth, abs(effectiveBitWidth));
        }
        else
        {
            return runUnderApproximation(transformer, effectiveBitWidth, abs(effectiveBitWidth));
        }
    }

    BDD returned = transformer.Proccess();
    return returned.IsZero() ? UNSAT : SAT;
}

Result Solver::Solve(z3::expr expr, Approximation approximation, unsigned int effectiveBitWidth)
{
    ExprSimplifier simplifier(expr.ctx(), m_propagateUncoinstrained);
    expr = simplifier.Simplify(expr);

    return getResult(expr, approximation, effectiveBitWidth);
}

Result Solver::solverThread(z3::expr expr, Approximation approximation, unsigned int effectiveBitWidth)
{
    m_z3context.lock();
    z3::context ctx;
    auto translated = z3::to_expr(ctx, Z3_translate(expr.ctx(), expr, ctx));
    m_z3context.unlock();

    auto res = getResult(translated, approximation, effectiveBitWidth);

    if (res == SAT || res == UNSAT)
    {
	std::unique_lock<std::mutex> lk(m);
	resultComputed = true;
	result = res;
	doneCV.notify_one();
    }

    return res;
}

Result Solver::SolveParallel(z3::expr expr)
{
    ExprSimplifier simplifier(expr.ctx(), m_propagateUncoinstrained);
    expr = simplifier.Simplify(expr);

    auto main = std::thread( [this,expr] { solverThread(expr); } );
    main.detach();
    auto under = std::thread( [this,expr] { solverThread(expr, UNDERAPPROXIMATION); } );
    under.detach();
    auto over = std::thread( [this,expr] { solverThread(expr, OVERAPPROXIMATION); } );
    over.detach();

    std::unique_lock<std::mutex> lk(m);
    while (!resultComputed)
    {
	doneCV.wait(lk);
    }

    return result;
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
	    if (lastBW == 1)
	    {
		Result approxResult = runFunction(transformer, lastBW, prec);
		if (approxResult == reliableResult || transformer.IsPreciseResult())
		{
		    return approxResult;
		}

		bool approxHappened = transformer.OperationApproximationHappened();

		approxResult = runFunction(transformer, -1, prec);
		if (approxResult == reliableResult || transformer.IsPreciseResult())
		{
		    return approxResult;
		}

		if (approxHappened || transformer.OperationApproximationHappened())
		{
		    prec *= 2;
		    continue;
		}

		lastBW++;
	    }

	    for (int bw = lastBW; bw <= 32; bw += 2)
	    {
		Result approxResult = runFunction(transformer, bw, prec);
		if (approxResult == reliableResult || transformer.IsPreciseResult())
		{
		    return approxResult;
		}

		bool approxHappened = transformer.OperationApproximationHappened();

		if (m_approximationMethod == VARIABLES || m_approximationMethod == BOTH)
		{
		    approxResult = runFunction(transformer, -bw, prec);
		    if (approxResult == reliableResult || transformer.IsPreciseResult())
		    {
			return approxResult;
		    }
		}

		if (approxHappened || transformer.OperationApproximationHappened())
		{
		    lastBW = bw;
		    break;
		}

		lastBW = bw;
	    }

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
