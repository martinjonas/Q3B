#ifndef UNCONSTRAINEDVARIABLESIMPLIFIER_H
#define UNCONSTRAINEDVARIABLESIMPLIFIER_H

#include "z3++.h"
#include <map>
#include <vector>
#include <string>

enum BoundType { EXISTENTIAL, UNIVERSAL };

class UnconstrainedVariableSimplifier
{
public:
    UnconstrainedVariableSimplifier(z3::context &ctx, z3::expr expr) : expression(expr)
    {
      this->context = &ctx;

      variableCounts = countVariableOccurences(expression, std::vector<std::string>(), true).first;
    }

    void PrintUnconstrained()
    {
        bool allConstrained = true;
        for (auto &item : variableCounts)
        {
            std::cout << "var " << item.first << " - " << item.second << " times" << std::endl;

            if (item.second == 1)
            {
                allConstrained = false;
                std::cout << "Unconstrained variable: " << item.first << std::endl;
            }
        }
        if (allConstrained) std::cout << "All variables constrained" << std::endl;
    }

    void SimplifyOnce()
    {
        expression = simplifyOnce(expression, {}, true);
    }

    z3::expr GetExpr() const { return expression; }

    void SimplifyIte();

private:
    z3::context* context;
    z3::expr expression;

    std::map<const Z3_ast, std::pair<std::map<std::string, int>, std::vector<std::string>>> subformulaVariableCounts;
    std::map<const Z3_ast, int> subformulaMaxDeBruijnIndices;
    std::map<std::string, int> variableCounts;

    std::map<const Z3_ast, std::pair<z3::expr, std::vector<std::pair<std::string, BoundType>>>> simplificationCache;

    std::pair<std::map<std::string, int>, int> countVariableOccurences(z3::expr, std::vector<std::string>, bool);

    z3::expr simplifyOnce(z3::expr, std::vector<std::pair<std::string, BoundType>>, bool);
    bool isUnconstrained(z3::expr, std::vector<std::pair<std::string, BoundType>>&);
    bool isVar(z3::expr);
    bool isBefore(z3::expr, z3::expr);
    BoundType getBoundType(z3::expr, std::vector<std::pair<std::string, BoundType>>&);
};

#endif // UNCONSTRAINEDVARIABLESIMPLIFIER_H
