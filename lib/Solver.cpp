#include "Solver.h"
#include "ExprSimplifier.h"
#include "TermConstIntroducer.h"

#include <thread>
#include <functional>

std::mutex Solver::m;
std::mutex Solver::m_z3context;

Result Solver::getResult(z3::expr expr, Approximation approximation, int effectiveBitWidth)
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

Result Solver::Solve(z3::expr expr, Approximation approximation, int effectiveBitWidth)
{
    m_z3context.lock();
    ExprSimplifier simplifier(expr.ctx(), m_propagateUncoinstrained);
    expr = simplifier.Simplify(expr);
    m_z3context.unlock();

    if (approximation == OVERAPPROXIMATION)
    {
	TermConstIntroducer tci(expr.ctx());
	expr = tci.FlattenMul(expr);
    }

    return getResult(expr, approximation, effectiveBitWidth);
}

Result Solver::solverThread(z3::expr expr, Approximation approximation, int effectiveBitWidth)
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

    TermConstIntroducer tci(expr.ctx());
    auto overExpr = tci.FlattenMul(expr);

    auto main = std::thread( [this,expr] { solverThread(expr); } );
    main.detach();
    auto under = std::thread( [this,expr] { solverThread(expr, UNDERAPPROXIMATION); } );
    under.detach();
    auto over = std::thread( [this,overExpr] { solverThread(overExpr, OVERAPPROXIMATION); } );
    over.detach();

    std::unique_lock<std::mutex> lk(m);
    while (!resultComputed)
    {
	doneCV.wait(lk);
    }

    return result;
}

Result Solver::runOverApproximation(ExprToBDDTransformer &transformer, int bitWidth, int precision)
{
    transformer.setApproximationType(SIGN_EXTEND);

    auto returned = transformer.ProcessOverapproximation(bitWidth, precision);

    auto result = returned.value.IsZero() ? UNSAT : SAT;
    if (result == UNSAT || transformer.IsPreciseResult())
    {
	return result;
    }

    auto model = transformer.GetModel(returned.value);
    m_z3context.lock();
    auto substituted = substituteModel(transformer.expression, model).simplify();
    m_z3context.unlock();

    if (substituted.hash() != transformer.expression.hash())
    {
	Solver validatingSolver(true);
	validatingSolver.SetReorderType(NO_REORDER);
	validatingSolver.SetApproximationMethod(m_approximationMethod);
	validatingSolver.SetLimitBddSizes(m_limitBddSizes);

	if (validatingSolver.Solve(substituted, UNDERAPPROXIMATION, 1) == SAT)
	{
	    return SAT;
	}
    }

    return UNKNOWN;
}

Result Solver::runUnderApproximation(ExprToBDDTransformer &transformer, int bitWidth, int precision)
{
    transformer.setApproximationType(ZERO_EXTEND);

    auto returned = transformer.ProcessUnderapproximation(bitWidth, precision);
    auto result = returned.value.IsZero() ? UNSAT : SAT;

    if (result == SAT || transformer.IsPreciseResult())
    {
	return result;
    }

    return UNKNOWN;
}

Result Solver::runWithApproximations(ExprToBDDTransformer &transformer, Approximation approximation)
{
    //TODO: Check if returned results (sat for overapproximation, unsat for underapproximation) are correct instead of returning unknown.

    assert (approximation != NO_APPROXIMATION);

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
	    if (prec > 2 && approximation == OVERAPPROXIMATION)
	    {
		Result approxResult = runFunction(transformer, 32, prec);
		if (approxResult != UNKNOWN)
		{
		    return approxResult;
		}
	    }

	    if (lastBW == 1)
	    {
		Result approxResult = runFunction(transformer, lastBW, prec);
		if (approxResult != UNKNOWN)
		{
		    return approxResult;
		}

		bool approxHappened = transformer.OperationApproximationHappened();

		approxResult = runFunction(transformer, -1, prec);
		if (approxResult != UNKNOWN)
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
		if (approxResult != UNKNOWN)
		{
		    return approxResult;
		}

		bool approxHappened = transformer.OperationApproximationHappened();

		if (m_approximationMethod == VARIABLES || m_approximationMethod == BOTH)
		{
		    approxResult = runFunction(transformer, -bw, prec);
		    if (approxResult != UNKNOWN)
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
	if (approxResult != UNKNOWN)
	{
	    return approxResult;
	}

	approxResult = runFunction(transformer, -1, 0);
	if (approxResult != UNKNOWN)
	{
	    return approxResult;
	}

	for (int bw = 2; bw < 32; bw += 2)
	{
	    approxResult = runFunction(transformer, bw, 0);
	    if (approxResult != UNKNOWN)
	    {
		return approxResult;
	    }

	    approxResult = runFunction(transformer, -bw, 0);
	    if (approxResult != UNKNOWN)
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

z3::expr Solver::substituteModel(z3::expr e, std::map<std::string, std::vector<bool>> model)
{
    auto &context = e.ctx();
    z3::expr_vector consts(context);
    z3::expr_vector vals(context);

    for (auto &varModel : model)
    {
	auto bitwidth = varModel.second.size();
	z3::expr c = context.bv_const(varModel.first.c_str(), bitwidth);

	std::stringstream ss;
	for (auto bit : varModel.second)
	{
	    ss << bit;
	}

	unsigned int value = stoull(ss.str(), 0, 2);

	consts.push_back(c);
	vals.push_back(context.bv_val(value, varModel.second.size()));

	if (bitwidth == 1)
	{
	    consts.push_back(context.bool_const(varModel.first.c_str()));
	    vals.push_back(context.bool_val(varModel.second[0]));
	}
    }

    return e.substitute(consts, vals);
}
