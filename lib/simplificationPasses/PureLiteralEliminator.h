#pragma once

#include <set>
#include <vector>

#include "z3++.h"

#include "../SimplificationPass.h"

enum Polarity { POSITIVE, NEGATIVE, BOTH_POLARITIES };

class PureLiteralEliminator : public SimplificationPass
{
public:
    PureLiteralEliminator(z3::context &ctx) : context(&ctx) { };
    z3::expr Apply(z3::expr&); //override;
    void ReconstructModel(Model &model) override;

private:
    z3::context* context;

    std::set< std::tuple< const Z3_ast, bool > > processedPolaritiesCache;
    std::map< std::string, Polarity > variablePolarities;
    void getVariablePolarities(const z3::expr&, bool);

    std::vector<std::pair<z3::expr, z3::expr>> appliedSubstitutions;
};
