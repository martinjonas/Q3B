#ifndef BDDSOLVER_H
#define BDDSOLVER_H

#include <z3++.h>
#include "cudd.h"
#include <cuddObj.hh>
#include "ExprToBDDTransformer.h"
#include "Config.h"
#include "Model.h"

#include <mutex>
#include <condition_variable>
#include <atomic>

enum Result { SAT, UNSAT, UNKNOWN, NORESULT };

class Solver
{
public:
    Solver(Config config) : config(config) { }

    Result Solve(z3::expr, Approximation approximation = NO_APPROXIMATION, int effectiveBitWidth = 0);
    Result SolveParallel(z3::expr);
    Model GetModel() const;

    static std::mutex m_z3context;
    static std::atomic<bool> resultComputed;

private:
    Config config;

    Result runUnderApproximation(ExprToBDDTransformer&, int, int);
    Result runOverApproximation(ExprToBDDTransformer&, int, int);

    Result runWithApproximations(ExprToBDDTransformer&, Approximation);
    Result runWithOverApproximations(ExprToBDDTransformer&);
    Result runWithUnderApproximations(ExprToBDDTransformer&);

    Result getResult(z3::expr, Approximation approximation = NO_APPROXIMATION, int effectiveBitWidth = 0);
    static Result solverThread(z3::expr, Config config, Approximation approximation = NO_APPROXIMATION, int effectiveBitWidth = 0);

    static std::atomic<Result> globalResult;
    static Model model;
    Model threadModel;
    static std::mutex m;
    static std::mutex m_res;
    static std::condition_variable doneCV;
};

#endif // BDDSOLVER_H
