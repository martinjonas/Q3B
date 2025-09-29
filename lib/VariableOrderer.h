#ifndef VARIABLEORDERER_H
#define VARIABLEORDERER_H

#include "UnionFind.cpp"
#include <list>
#include <map>
#include <set>
#include <string>
#include <vector>
#include <z3++.h>

typedef std::pair<std::string, int> var;

class VariableOrderer
{
private:
    std::set<var> vars;
    std::map<std::string, int> varIndices;
    UF *unionFind = NULL;
    z3::context *context;

    bool MergeByExpression(const z3::expr &,
                           std::vector<std::string> boundVars);
    void MarkDependent(const std::string &, const std::string &);
    void MergeVars(const std::set<std::string> &);
    void MergeAllVarsInExpression(const z3::expr &,
                                  std::vector<std::string> boundVars);
    std::set<std::string> GetVars(const z3::expr &, std::vector<std::string>);

    std::map<const Z3_ast, std::vector<std::string>>
        processedMergedSubformulaCache;
    std::map<const Z3_ast,
             std::pair<std::set<std::string>, std::vector<std::string>>>
        processedVarsCache;

public:
    VariableOrderer(const std::set<var> &, z3::context &);
    void OrderFor(const z3::expr &);
    void MergeAll();

    std::vector<std::list<var>> GetOrdered() const;
};

#endif // VARIABLEORDERER_H
