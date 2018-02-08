#ifndef BDDSOLVER_H
#define BDDSOLVER_H

#include <z3++.h>
// #include <bdd.h>
#include "cudd.h"
#include <cuddObj.hh>
#include "ExprToBDDTransformer.h"

#include <mutex>
#include <condition_variable>

enum Result { SAT, UNSAT, UNKNOWN };

class Solver
{
public:
    Solver(bool propagateUncoinstrained) :
    	m_propagateUncoinstrained(propagateUncoinstrained), m_negateMul(false), m_initialOrder(HEURISTIC) { }

    Result Solve(z3::expr, Approximation approximation = NO_APPROXIMATION, unsigned int effectiveBitWidth = 0);
    Result SolveParallel(z3::expr);

    void SetReorderType(ReorderType reorderType)
    {
        m_reorderType = reorderType;
    }

    void SetInitialOrder(InitialOrder initialOrder)
    {
        m_initialOrder = initialOrder;
    }

    void SetNegateMul(bool negateMul)
    {
	m_negateMul = negateMul;
    }

    void SetApproximationMethod(ApproximationMethod am)
    {
	m_approximationMethod = am;
    }

    void SetLimitBddSizes(bool limitBddSizes)
    {
	m_limitBddSizes = limitBddSizes;
    }

    void SetUseDontCares(bool dontCare)
    {
	m_useDontCares = dontCare;
    }

private:
    bool m_propagateUncoinstrained;
    bool m_negateMul;
    bool m_limitBddSizes;
    bool m_useDontCares;
    ReorderType m_reorderType;
    InitialOrder m_initialOrder;
    ApproximationMethod m_approximationMethod;

    Result runUnderApproximation(ExprToBDDTransformer&, int, unsigned int);
    Result runOverApproximation(ExprToBDDTransformer&, int, unsigned int);

    Result runWithApproximations(ExprToBDDTransformer&, Approximation);
    Result runWithOverApproximations(ExprToBDDTransformer&);
    Result runWithUnderApproximations(ExprToBDDTransformer&);

    Result getResult(z3::expr, Approximation approximation = NO_APPROXIMATION, unsigned int effectiveBitWidth = 0);
    Result solverThread(z3::expr, Approximation approximation = NO_APPROXIMATION, unsigned int effectiveBitWidth = 0);

    Result result = UNKNOWN;
    bool resultComputed = false;
    std::mutex m;
    std::mutex m_z3context;
    std::condition_variable doneCV;
};

#endif // BDDSOLVER_H
