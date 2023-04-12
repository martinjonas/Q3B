#include "Solver.h"
#include "ExprSimplifier.h"
#include "TermConstIntroducer.h"
#include "Logger.h"

#include <thread>
#include <functional>
#include <sstream>

std::mutex Solver::m;
std::mutex Solver::m_res;
std::mutex Solver::m_z3context;

std::atomic<Result> Solver::globalResult = UNKNOWN;
std::map<std::string, std::vector<bool>> Solver::model;
//std::map<std::string, std::vector<bool>> Solver::threadModel;

std::atomic<bool> Solver::resultComputed = false;
std::condition_variable Solver::doneCV;

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

    ExprToBDDTransformer transformer(expr.ctx(), expr, config);

    if (approximation == UNDERAPPROXIMATION || approximation == OVERAPPROXIMATION)
    {
        if (effectiveBitWidth == 0)
        {
            return runWithApproximations(transformer, approximation);
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
    if (!returned.IsZero() && config.produceModels)
    {
        threadModel = transformer.GetModel(returned, PRECISE_BDD);
        model = threadModel;
    }
    return returned.IsZero() ? UNSAT : SAT;
}

Result Solver::Solve(z3::expr expr, Approximation approximation, int effectiveBitWidth)
{
    if (!config.validatingSolver)
    {
        Solver::resultComputed = false;
    }
    Logger::Log("Solver", "Simplifying formula.", 1);
    m_z3context.lock();
    ExprSimplifier simplifier(expr.ctx(), config.propagateUnconstrained, config.goalUnconstrained);
    simplifier.SetProduceModels(config.produceModels);
    expr = simplifier.Simplify(expr);
    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH)
    {
        expr = simplifier.StripToplevelExistentials(expr);
    }

    m_z3context.unlock();

    bool negated = false;
    if (config.flipUniversalQuantifier &&
        expr.is_quantifier() &&
        Z3_is_quantifier_forall(expr.ctx(), (Z3_ast)expr) &&
        simplifier.isSentence(expr))
    {
        Logger::Log("Solver", "Negating universal formula.", 1);
        negated = true;
        expr = simplifier.negate(expr);
        expr = simplifier.PushNegations(expr);
        expr = simplifier.StripToplevelExistentials(expr);

        if (approximation == OVERAPPROXIMATION) approximation = UNDERAPPROXIMATION;
        else if (approximation == UNDERAPPROXIMATION) approximation = OVERAPPROXIMATION;
    }

    if (approximation == OVERAPPROXIMATION)
    {
	Logger::Log("Solver", "Introducing mul constants.", 1);
	TermConstIntroducer tci(expr.ctx());
        if (config.addCongruences)
        {
            expr = tci.FlattenMul(expr);
        }
    }

    Logger::Log("Solver", "Starting solver.", 1);
    auto result = getResult(expr, approximation, effectiveBitWidth);
    if (negated)
    {
        Logger::Log("Solver", "Flipping result of the negated formula.", 1);
        if (result == SAT) result = UNSAT;
        else if (result == UNSAT) result = SAT;
    }
    return result;
}

std::map<std::string, std::vector<bool>> Solver::GetModel() const
{
    return Solver::model;
}

Result Solver::solverThread(z3::expr expr, Config config, Approximation approximation, int effectiveBitWidth)
{
    Solver solver(config);
    m_z3context.lock();
    z3::context ctx;
    auto translated = z3::to_expr(ctx, Z3_translate(expr.ctx(), expr, ctx));
    m_z3context.unlock();

    Result res = UNKNOWN;
    try
    {
        res = solver.getResult(translated, approximation, effectiveBitWidth);
    }
    catch (std::logic_error& e)
    {
        Logger::Log("Solver", e.what(), 1);
    }

    if (res == SAT || res == UNSAT)
    {
	std::stringstream ss;

	if (approximation == NO_APPROXIMATION)
	{
	    Logger::Log("Solver", "Decided by the base solver", 1);
	}

        std::unique_lock<std::mutex> lk(m_res);
        if (!resultComputed)
        {
            resultComputed = true;
            Solver::globalResult = res;
            if (res == SAT && config.produceModels)
            {
                Solver::model = solver.threadModel;
            }
            doneCV.notify_one();
        }
        else
        {
            return UNKNOWN;
        }
    }

    return res;
}

Result Solver::SolveParallel(z3::expr expr) {
    Solver::resultComputed = false;
    Logger::Log("Solver", "Simplifying formula.", 1);
    ExprSimplifier simplifier(expr.ctx(), config.propagateUnconstrained, config.goalUnconstrained);
    simplifier.SetProduceModels(config.produceModels);
    expr = simplifier.Simplify(expr);
    if (config.approximationMethod == OPERATIONS || config.approximationMethod == BOTH) {
        expr = simplifier.StripToplevelExistentials(expr);
    }

    if (expr.is_const()) {
        if (expr.is_app() && expr.decl().decl_kind() == Z3_OP_TRUE) {
            Logger::Log("Solver", "Solved by simplifications.", 1);
            return SAT;
        } else if (expr.is_app() && expr.decl().decl_kind() == Z3_OP_FALSE) {
            Logger::Log("Solver", "Solved by simplifications.", 1);
            return UNSAT;
        }
    }

    bool negated = false;
    if (config.flipUniversalQuantifier &&
        expr.is_quantifier() &&
        Z3_is_quantifier_forall(expr.ctx(), (Z3_ast) expr) &&
        simplifier.isSentence(expr)) {
        Logger::Log("Solver", "Negating universal formula.", 1);
        negated = true;
        expr = simplifier.negate(expr);
        expr = simplifier.PushNegations(expr);
        expr = simplifier.StripToplevelExistentials(expr);
    }

    Logger::Log("Solver", "Introducing mul constants.", 1);
    TermConstIntroducer tci(expr.ctx());
    auto overExpr = config.addCongruences ? tci.FlattenMul(expr) : expr;

    Logger::Log("Solver", "Starting solver threads.", 1);
    auto config = this->config;
    auto main = std::thread(Solver::solverThread, expr, config, NO_APPROXIMATION, 0);
    auto under = std::thread(Solver::solverThread, expr, config, UNDERAPPROXIMATION, 0);
    auto over = std::thread(Solver::solverThread, overExpr, config, OVERAPPROXIMATION, 0);

    std::unique_lock<std::mutex> lk(m);
    while (!resultComputed) {
        doneCV.wait(lk);
    }

    if (negated) {
        Logger::Log("Solver", "Flipping result of the negated formula.", 1);
        if (globalResult == SAT) globalResult = UNSAT;
        else if (globalResult == UNSAT) globalResult = SAT;
    }

    main.join();
    over.join();
    under.join();

    return globalResult;
}

Result Solver::runOverApproximation(ExprToBDDTransformer &transformer, int bitWidth, int precision)
{
    if (resultComputed) return UNKNOWN;
    transformer.setApproximationType(SIGN_EXTEND);

    std::stringstream ss;
    ss << "Trying bit-width " << bitWidth << ", precision " << precision;
    Logger::Log("Overapproximating solver", ss.str(), 5);

    auto returned = transformer.ProcessOverapproximation(bitWidth, precision);

    auto result = returned.IsZero() ? UNSAT : SAT;
    if (result == UNSAT)
    {
        Logger::Log("Solver", "Decided by overapproximation", 1);
        std::stringstream rss;
        rss << "Final bit-width " << bitWidth << ", precision " << precision;
        Logger::Log("Overapproximating solver", rss.str(), 1);
        return result;
    }

    if (Solver::resultComputed) return UNKNOWN;

    transformer.PrintNecessaryValues(returned);

    if (config.checkModels)
    {
        if (Solver::resultComputed) return UNKNOWN;

        auto lower = returned.ForgetZeros();                        // guaranteed not to be a const [0]
        auto model = lower.IsUnknown()
                ? transformer.GetModel(returned, OVER_APPROX_BDD)   // no [1] target, try [?]
                : transformer.GetModel(lower, UNDER_APPROX_BDD);    // go for the [1] target

        m_z3context.lock();
        auto substituted = substituteModel(transformer.expression, model).simplify();
        m_z3context.unlock();

        if (substituted.hash() != transformer.expression.hash())
        {
            Logger::Log("Overapproximating solver", "Validating model", 5);

            Config validatingConfig;
            validatingConfig.propagateUnconstrained = true;
            validatingConfig.approximationMethod = config.approximationMethod;
            validatingConfig.validatingSolver = true;

            Solver validatingSolver(validatingConfig);

            if (validatingSolver.Solve(substituted, UNDERAPPROXIMATION, 1) == SAT)
            {
                Logger::Log("Solver", "Decided by overapproximation", 1);
                std::stringstream rss;
                rss << "Final bit-width " << bitWidth << ", precision " << precision;
                Logger::Log("Overapproximating solver", rss.str(), 1);
                if (config.produceModels)
                {
                    threadModel = model;
                }
                return SAT;
            }
        }
    }

    return UNKNOWN;
}

Result Solver::runUnderApproximation(ExprToBDDTransformer &transformer, int bitWidth, int precision)
{
    if (resultComputed) return UNKNOWN;
    transformer.setApproximationType(ZERO_EXTEND);

    std::stringstream ss;
    ss << "Trying bit-width " << bitWidth << ", precision " << precision;
    Logger::Log("Underapproximating solver", ss.str(), 5);

    auto returned = transformer.ProcessUnderapproximation(bitWidth, precision);
    auto lower = returned.ForgetZeros();
    auto result = lower.IsUnknown() ? UNSAT : SAT;

    if (result == SAT && !resultComputed)
    {
        Logger::Log("Solver", "Decided by underapproximation", 1);
        std::stringstream rss;
        rss << "Final bit-width " << bitWidth << ", precision " << precision;
        Logger::Log("Underapproximating solver", rss.str(), 1);

        if (config.produceModels)
        {
            threadModel = transformer.GetModel(lower, UNDER_APPROX_BDD);
        }

        return result;
    }

    return UNKNOWN;
}


Result Solver::runWithApproximations(ExprToBDDTransformer &transformer, Approximation approximation)
{
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
	while (prec != 0 && !resultComputed)
	{
	    if (prec == 4 && approximation == OVERAPPROXIMATION)
	    {
		Result approxResult = runFunction(transformer, 128, 2);
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

		if (approxHappened || transformer.OperationApproximationHappened())
		{
		    prec *= 4;
		    continue;
		}

		approxResult = runFunction(transformer, -1, prec);
		if (approxResult != UNKNOWN)
		{
		    return approxResult;
		}

		approxHappened = transformer.OperationApproximationHappened();

		if (approxHappened || transformer.OperationApproximationHappened())
		{
		    prec *= 4;
		    continue;
		}

		lastBW++;
	    }

	    for (int bw = lastBW; bw <= 128; bw += 2)
	    {
                if (resultComputed) return UNKNOWN;
                Result approxResult = runFunction(transformer, bw, prec);
                if (approxResult != UNKNOWN)
                {
                    return approxResult;
                }

                bool approxHappened = transformer.OperationApproximationHappened();
                if (approxHappened || transformer.OperationApproximationHappened())
                {
                    lastBW = bw;
                    break;
                }

                lastBW = bw;
            }

            prec *= 4;
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
            if (resultComputed) return UNKNOWN;
            approxResult = runFunction(transformer, bw, 0);
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


z3::expr Solver::substituteModel(z3::expr& e, const std::map<std::string, std::vector<bool>>& model)
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

	unsigned long long value = 0;
	if (bitwidth <= 8 * sizeof(unsigned long long))
	{
	    value = stoull(ss.str(), 0, 2);
	}

	consts.push_back(c);
        vals.push_back(context.bv_val(static_cast<uint64_t>(value), bitwidth));

	if (bitwidth == 1)
	{
	    consts.push_back(context.bool_const(varModel.first.c_str()));
	    vals.push_back(context.bool_val(varModel.second[0]));
	}
    }

    return e.substitute(consts, vals);
}
