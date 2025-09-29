#pragma once

#include "Model.h"
#include "z3++.h"

struct SimplificationPass {
    // virtual z3::expr Apply(const z3::expr&) = 0;
    virtual void ReconstructModel(Model &model) = 0;

    virtual ~SimplificationPass() {};
};
