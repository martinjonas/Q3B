#ifndef CONFIG_H
#define CONFIG_H

enum ApproximationMethod { NONE, VARIABLES, OPERATIONS, BOTH };
enum InitialOrder { INTERLEAVE_ALL, HEURISTIC, SEQUENTIAL };
enum ReorderType { NO_REORDER, WIN2, WIN2_ITE, WIN3, WIN3_ITE, SIFT, SIFT_ITE };

struct Config
{
    ApproximationMethod approximationMethod = VARIABLES;
    bool limitBddSizes = false;

    InitialOrder initialOrder = HEURISTIC;
    ReorderType reorderType = NO_REORDER;

    bool negateMul = false;

    bool propagateUnconstrained = false;

    // FROM MASTER:
    bool goalUnconstrained = true;

    bool useDontCares = false;

    bool checkModels = false;

    bool flipUniversalQuantifier = false;

    // FROM MASTER:
    bool propagateNecessaryBits = true;

    // FROM MASTER:
    bool produceModels = false;
    bool validatingSolver = false;
};

#endif