#include "Approximated.h"

Precision operator && (const Precision &l, const Precision &r)
{
    return l == PRECISE && r == PRECISE ? PRECISE : APPROXIMATED;
}
