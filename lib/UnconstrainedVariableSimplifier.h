#ifndef UNCONSTRAINEDVARIABLESIMPLIFIER_H
#define UNCONSTRAINEDVARIABLESIMPLIFIER_H

#include "z3++.h"
#include <iostream>
#include <list>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>

#include "HashUtils.h"
#include "SimplificationPass.h"
enum BoundType { EXISTENTIAL, UNIVERSAL };
enum Goal { SIGN_MIN, SIGN_MAX, UNSIGN_MIN, UNSIGN_MAX, NONE };

typedef std::tuple<std::string, BoundType, int> BoundVar;

namespace std
{
template <> struct hash<BoundVar> {
    size_t operator()(const BoundVar &p) const
    {
        auto h1 = std::hash<std::string>{}(std::get<0>(p));
        auto h2 = 1 + std::get<1>(p);
        auto h3 = std::get<2>(p);

        return h1 ^ h2 ^ h3;
    }
};

template <> struct hash<std::vector<BoundVar>> {
    std::size_t operator()(const std::vector<BoundVar> &vec) const
    {
        std::size_t seed = vec.size();
        for (auto &i : vec) {
            seed ^= std::hash<BoundVar>{}(i) + 0x9e3779b9 + (seed << 6) +
                    (seed >> 2);
        }
        return seed;
    }
};
} // namespace std

class UnconstrainedVariableSimplifier : public SimplificationPass
{
public:
    UnconstrainedVariableSimplifier(z3::context &ctx, z3::expr expr)
        : expression(expr)
    {
        this->context = &ctx;
    }

    void PrintUnconstrained()
    {
        std::cout << "------" << std::endl;
        bool allConstrained = true;

        for (auto &item : variableCounts) {
            if (item.second == 1) {
                allConstrained = false;
                std::cout << "Unconstrained variable: " << item.first
                          << std::endl;
            }
        }
        if (allConstrained)
            std::cout << "All variables constrained" << std::endl;
        std::cout << "------" << std::endl;
    }

    void SimplifyOnce()
    {
        expression = simplifyOnce(expression, {}, true, NONE);
    }

    z3::expr GetExpr() const { return expression; }

    void SimplifyIte();

    void SetDagCounting(bool dagCounting) { this->dagCounting = dagCounting; }

    void SetGoalUnconstrained(bool goalUnconstrained)
    {
        this->goalUnconstrained = goalUnconstrained;
    }

    void SetPreserveEquivalence(bool preserveEquivalence)
    {
        this->preserveEquivalence = preserveEquivalence;
    }

    void MarkConstrained(std::set<std::string> vars)
    {
        forcedConstrained = vars;
    }

    void ForceGoal(Goal goal) { forcedGoal = goal; }

    void ReconstructModel(Model &model) override
    {
        std::cout << "Warning: model reconstruction for unconstrained "
                     "simplifications is not implemented \n";
    }

private:
    z3::context *context;
    z3::expr expression;
    bool preserveEquivalence;

    std::unordered_map<std::tuple<z3::expr, bool, Goal>,
                       std::map<std::string, int>>
        subformulaVariableCounts;
    std::unordered_map<std::pair<z3::expr, std::vector<BoundVar>>, int>
        subformulaMaxLevels;
    std::map<std::string, int> variableCounts;

    typedef std::unordered_map<z3::expr,
                               std::pair<z3::expr, const std::vector<BoundVar>>>
        cacheMapType;

    cacheMapType trueSimplificationCache;
    cacheMapType falseSimplificationCache;

    std::map<std::string, int> countVariableOccurences(z3::expr, bool, Goal);
    std::map<std::string, int> countFormulaVarOccurences(z3::expr);
    void addCounts(const std::map<std::string, int> &,
                   std::map<std::string, int> &);
    void maxCounts(std::map<std::string, int> &&, std::map<std::string, int> &);
    bool allConstrained(std::map<std::string, int> &);
    int getMaxLevel(z3::expr, const std::vector<BoundVar> &, bool);

    z3::expr simplifyOnce(z3::expr, std::vector<BoundVar>, bool, Goal);
    bool isUnconstrained(z3::expr, const std::vector<BoundVar> &) const;
    bool isVar(z3::expr) const;
    bool isBefore(z3::expr, z3::expr, const std::vector<BoundVar> &, bool);
    BoundType getBoundType(z3::expr, const std::vector<BoundVar> &);

    int getNumberOfLeadingZeroes(const z3::expr &);
    int lastBound = 0;

    bool dagCounting = false;
    bool goalUnconstrained = false;
    int cacheHits = 0;

    std::set<std::string> forcedConstrained;
    std::optional<Goal> forcedGoal;
};

#endif // UNCONSTRAINEDVARIABLESIMPLIFIER_H
