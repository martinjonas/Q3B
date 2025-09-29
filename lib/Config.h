#pragma once

enum ApproximationMethod { NONE, VARIABLES, OPERATIONS, BOTH };
enum ReorderType { NO_REORDER, WIN2, WIN2_ITE, WIN3, WIN3_ITE, SIFT, SIFT_ITE };
enum Approximations {
    NO_APPROXIMATIONS,
    ONLY_UNDERAPPROXIMATIONS,
    ONLY_OVERAPPROXIMATIONS,
    ALL_APPROXIMATIONS
};

struct Config {
    ApproximationMethod approximationMethod = BOTH;
    Approximations approximations = ALL_APPROXIMATIONS;
    int precision = 0;

    ReorderType reorderType = SIFT;

    bool propagateUnconstrained = true;
    bool goalUnconstrained = true;

    bool useDontCares = false;

    bool checkModels = true;
    bool addCongruences = true;

    bool flipUniversalQuantifier = false;
    bool propagateNecessaryBits = true;

    bool produceModels = false;
    bool validatingSolver = false;
};
