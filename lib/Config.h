#pragma once

enum ApproximationMethod { NONE, VARIABLES, OPERATIONS, BOTH };
enum InitialOrder { INTERLEAVE_ALL, HEURISTIC, SEQUENTIAL };
enum ReorderType { NO_REORDER, WIN2, WIN2_ITE, WIN3, WIN3_ITE, SIFT, SIFT_ITE };

struct Config
{
    ApproximationMethod approximationMethod = VARIABLES;

    InitialOrder initialOrder = HEURISTIC;
    ReorderType reorderType = NO_REORDER;

    bool propagateUnconstrained = false;

    bool useDontCares = false;

    bool checkModels = false;

    bool flipUniversalQuantifier = false;

    bool propagateNecessaryBits = false;
};
