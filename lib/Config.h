#pragma once

enum ApproximationMethod { NONE, VARIABLES, OPERATIONS, BOTH };
enum InitialOrder { INTERLEAVE_ALL, HEURISTIC, SEQUENTIAL };
enum ReorderType { NO_REORDER, WIN2, WIN2_ITE, WIN3, WIN3_ITE, SIFT, SIFT_ITE };

struct Config
{
    ApproximationMethod approximationMethod = BOTH;

    InitialOrder initialOrder = HEURISTIC;
    ReorderType reorderType = SIFT;

    bool propagateUnconstrained = true;
    bool goalUnconstrained = true;

    bool useDontCares = false;

    bool checkModels = true;

    bool flipUniversalQuantifier = false;

    bool propagateNecessaryBits = true;
};
