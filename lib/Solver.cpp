#include "Solver.h"
#include "ExprSimplifier.h"
#include "TermConstIntroducer.h"
#include "Logger.h"

#include <thread>
#include <functional>
#include <sstream>

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
	std::string declName;

	{
	    std::unique_lock<std::mutex> lk(m_z3context);
	    declName = decl.name().str();
	}

	//TODO: if formula does not contain constants, conjunctions can
	//be also solved independently
        if (declName == "or")
        {
	    Logger::Log("Solver", "Toplevel disjunction, splitting.", 1);
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

    ExprToBDDTransformer transformer(expr.ctx(), expr, config);

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
    Logger::Log("Solver", "Simplifying formula.", 1);
    m_z3context.lock();
    ExprSimplifier simplifier(expr.ctx(), config.propagateUnconstrained);
    expr = simplifier.Simplify(expr);
    m_z3context.unlock();

    if (approximation == OVERAPPROXIMATION)
    {
	Logger::Log("Solver", "Introducing mul constants.", 1);
	TermConstIntroducer tci(expr.ctx());
	expr = tci.FlattenMul(expr);
    }

    Logger::Log("Solver", "Starting solver.", 1);
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
	std::stringstream ss;

	if (approximation == OVERAPPROXIMATION)
	{
	    Logger::Log("Solver", "Decided by an overapproximation", 1);
	}
	else if (approximation == UNDERAPPROXIMATION)
	{
	    Logger::Log("Solver", "Decided by an underapproximation", 1);
	}
	else
	{
	    Logger::Log("Solver", "Decided by the base solver", 1);
	}

	std::unique_lock<std::mutex> lk(m);
	resultComputed = true;
	result = res;
	doneCV.notify_one();
    }

    return res;
}

Result Solver::SolveParallel(z3::expr expr)
{
    Logger::Log("Solver", "Simplifying formula.", 1);
    ExprSimplifier simplifier(expr.ctx(), config.propagateUnconstrained);
    expr = simplifier.Simplify(expr);

    Logger::Log("Solver", "Introducing mul constants.", 1);
    TermConstIntroducer tci(expr.ctx());
    auto overExpr = tci.FlattenMul(expr);

    Logger::Log("Solver", "Starting solver threads.", 1);
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

    std::stringstream ss;
    ss << "Trying bit-width " << bitWidth << ", precision " << precision;
    Logger::Log("Overapproximating solver", ss.str(), 5);

    auto returned = transformer.ProcessOverapproximation(bitWidth, precision);

    auto result = returned.value.IsZero() ? UNSAT : SAT;
    if (result == UNSAT || transformer.IsPreciseResult())
    {
	return result;
    }

    if (config.checkModels)
    {
	auto model = transformer.GetModel(returned.value);
	m_z3context.lock();
	auto substituted = substituteModel(transformer.expression, model).simplify();
	m_z3context.unlock();

	if (substituted.hash() != transformer.expression.hash())
	{
	    Logger::Log("Overapproximating solver", "Validating model", 5);

	    Config validatingConfig;
	    validatingConfig.propagateUnconstrained = true;
	    validatingConfig.approximationMethod = config.approximationMethod;
	    validatingConfig.limitBddSizes = config.limitBddSizes;

	    Solver validatingSolver(validatingConfig);

	    if (validatingSolver.Solve(substituted, UNDERAPPROXIMATION, 1) == SAT)
	    {
		return SAT;
	    }
	}
    }

    return UNKNOWN;
}

Result Solver::runUnderApproximation(ExprToBDDTransformer &transformer, int bitWidth, int precision)
{
    transformer.setApproximationType(ZERO_EXTEND);

    std::stringstream ss;
    ss << "Trying bit-width " << bitWidth << ", precision " << precision;
    Logger::Log("Underapproximating solver", ss.str(), 5);

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

    if (config.approximationMethod == BOTH)
    {
	unsigned int prec = 1;
	unsigned int lastBW = 1;
	while (prec != 0)
	{
	    if (prec > 2 && prec <= 4 && approximation == OVERAPPROXIMATION)
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

		if (config.approximationMethod == VARIABLES || config.approximationMethod == BOTH)
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
    else if (config.approximationMethod == VARIABLES)
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

z3::expr Solver::substituteModel(z3::expr& e, const std::map<std::string, std::vector<bool>>& model) const
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
