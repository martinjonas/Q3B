#include "Solver.h"

bool BDDInterval::isInterrupted() const
{
    return Solver::resultComputed;
}
