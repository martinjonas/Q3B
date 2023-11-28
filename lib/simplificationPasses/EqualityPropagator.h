#pragma once

#include <vector>

#include "z3++.h"

#include "../SimplificationPass.h"

class EqualityPropagator : public SimplificationPass
{
public:
    EqualityPropagator(z3::context &ctx) : context(&ctx) { };
    z3::expr Apply(const z3::expr&); //override;
    void ReconstructModel(Model &model) override;

private:
    z3::context* context;

    bool getSubstitutableEquality(const z3::expr&, z3::expr*, z3::expr*);
    bool isVar(const z3::expr&) const;

    std::vector<std::pair<z3::expr, z3::expr>> appliedSubstitutions;
};
