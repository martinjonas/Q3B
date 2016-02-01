#ifndef BDDSOLVER_H
#define BDDSOLVER_H

#include <z3++.h>
#include <bdd.h>
#include "ExprToBDDTransformer.h"

enum Result { SAT, UNSAT, UNKNOWN };
enum Approximation { UNDERAPPROXIMATION, OVERAPPROXIMATION, NO_APPROXIMATION };

class Solver
{
public:
    Solver() : approximationType(NO_APPROXIMATION), effectiveBitWidth(0) { }
    Solver(bool propagateUncoinstrained) : approximationType(NO_APPROXIMATION), effectiveBitWidth(0), propagateUncoinstrained(propagateUncoinstrained) { }
    Result GetResult(z3::expr);

    void SetApproximation(Approximation approximation, int bitWidth)
    {
        approximation = approximation;
        bitWidth = bitWidth;
    }

    void SetReorderType(ReorderType reorderType)
    {
        reorderType = reorderType;
    }

private:
    Approximation approximationType;    
    int effectiveBitWidth;
    bool propagateUncoinstrained;
    ReorderType reorderType;

    void set_bdd();

    Result runUnderApproximation(ExprToBDDTransformer&, int);
    Result runOverApproximation(ExprToBDDTransformer&, int);

    Result runWithOverApproximations(ExprToBDDTransformer&);
    Result runWithUnderApproximations(ExprToBDDTransformer&);
};

#endif // BDDSOLVER_H
