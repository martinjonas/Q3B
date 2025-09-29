#include "VariableOrderer.h"
#include "Solver.h"
#include <algorithm>

using namespace std;
using namespace z3;

VariableOrderer::VariableOrderer(const std::set<var> &vars, z3::context &ctx)
    : vars(vars)
{
    this->context = &ctx;
    this->unionFind = new UF(vars.size());

    int i = 0;
    for (auto const &v : vars) {
        varIndices[v.first] = i;
        i++;
    }
}

void VariableOrderer::MergeVars(const std::set<std::string> &vars)
{
    if (vars.size() > 0) {
        for (auto const &v : vars) {
            MarkDependent(*vars.begin(), v);
        }
    }
}

void VariableOrderer::MergeAllVarsInExpression(
    const z3::expr &e, std::vector<std::string> boundVars)
{
    MergeVars(GetVars(e, boundVars));
}

bool VariableOrderer::MergeByExpression(const z3::expr &e,
                                        std::vector<std::string> boundVars)
{
    auto item = processedMergedSubformulaCache.find((Z3_ast)e);
    if (false && item != processedMergedSubformulaCache.end() &&
        item->second == boundVars) {
        return false;
    }

    processedMergedSubformulaCache.insert({(Z3_ast)e, boundVars});
    assert(e.is_bool());

    if (e.is_app()) {
        // cout << "APP: " << e << endl;
        func_decl f = e.decl();
        unsigned num = e.num_args();

        string functionName = f.name().str();
        // cout << "fun: " << functionName << endl;

        if (functionName == "not") {
            return MergeByExpression(e.arg(0), boundVars);
        } else if (functionName == "and" || functionName == "or") {
            bool allBool = true;
            std::set<std::string> varsToMerge;

            for (unsigned int i = 0; i < num; i++) {
                bool currentAllBool = MergeByExpression(e.arg(i), boundVars);
                if (currentAllBool) {
                    auto currentVars = GetVars(e.arg(i), boundVars);
                    varsToMerge.insert(currentVars.begin(), currentVars.end());
                }

                allBool &= currentAllBool;
            }

            // this actually degrades the performance
            // MergeVars(varsToMerge);

            return allBool;
        } else if (functionName == "iff") {
            bool b1 = MergeByExpression(e.arg(0), boundVars);
            bool b2 = MergeByExpression(e.arg(1), boundVars);

            if (b1 && b2) {
                // this actually degrades the performance
                // MergeAllVarsInExpression(e, boundVars);
            }

            return b1 && b2;
        } else if (functionName == "if") {
            bool b1 = MergeByExpression(e.arg(0), boundVars);
            bool b2 = MergeByExpression(e.arg(1), boundVars);
            bool b3 = MergeByExpression(e.arg(2), boundVars);

            if (b1 && b2 && b3) {
                // MergeAllVarsInExpression(e, boundVars);
            }

            return b1 && b2 && b3;
        } else {
            MergeAllVarsInExpression(e, boundVars);

            // cout << "function " << f.name().str() << endl;

            bool allBool = true;
            for (unsigned int i = 0; i < num; i++) {
                allBool &= e.arg(i).get_sort().is_bool();
            }

            return allBool && e.get_sort().is_bool();
        }
    } else if (e.is_quantifier()) {
        Z3_ast ast = (Z3_ast)e;

        int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

        for (int i = 0; i < boundVariables; i++) {
            Z3_symbol z3_symbol =
                Z3_get_quantifier_bound_name(*context, ast, i);

            symbol current_symbol(*context, z3_symbol);

            string c = current_symbol.str();
            boundVars.push_back(c);
        }

        MergeByExpression(e.body(), boundVars);
        return false;
    } else {
        return e.is_var() && e.get_sort().is_bool();
    }
}

void VariableOrderer::MergeAll()
{
    for (unsigned int i = 1; i < vars.size(); i++) {
        unionFind->merge(0, i);
    }
}

set<string> VariableOrderer::GetVars(const expr &e,
                                     std::vector<std::string> boundVars)
{
    set<string> vars;

    auto item = processedVarsCache.find((Z3_ast)e);
    if (item != processedVarsCache.end() &&
        (item->second).second == boundVars) {
        return (item->second).first;
    }

    if (e.is_var()) {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        vars.insert(boundVars.at(boundVars.size() - deBruijnIndex - 1));
        return vars;
    } else if (e.is_const() && !e.is_numeral()) {
        if (e.get_sort().is_bool() || e.get_sort().is_bv()) {
            if (e.is_app() && (e.decl().decl_kind() == Z3_OP_TRUE ||
                               e.decl().decl_kind() == Z3_OP_FALSE)) {
                return vars;
            }

            std::unique_lock<std::mutex> lk(Solver::m_z3context);
            vars.insert(e.to_string());
        }
    }
    if (e.is_app()) {
        func_decl f = e.decl();
        unsigned num = e.num_args();

        if (num != 0) {
            for (unsigned i = 0; i < num; i++) {
                set<string> currentVars = GetVars(e.arg(i), boundVars);
                vars.insert(currentVars.begin(), currentVars.end());

                processedVarsCache.insert(
                    {(Z3_ast)e.arg(i), {currentVars, boundVars}});
            }
        } else if (f.name() != NULL) {
            z3::sort s = f.range();

            if (s.is_bv() && !e.is_numeral()) {
                vars.insert(f.name().str());
            }
        }

        return vars;
    } else if (e.is_quantifier()) {
        Z3_ast ast = (Z3_ast)e;

        int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

        for (int i = 0; i < boundVariables; i++) {
            Z3_symbol z3_symbol =
                Z3_get_quantifier_bound_name(*context, ast, i);

            symbol current_symbol(*context, z3_symbol);

            string c = current_symbol.str();
            boundVars.push_back(c);
        }

        return GetVars(e.body(), boundVars);
        // bdd bodyBdd = getBDDFromExpr(e.body(), boundVars);
    }

    return vars;
}

void VariableOrderer::MarkDependent(const string &x, const string &y)
{
    int index1 = varIndices[x];
    int index2 = varIndices[y];
    unionFind->merge(index1, index2);
    // cout << "merging " << x << " " << y << endl;
}

void VariableOrderer::OrderFor(const z3::expr &expr)
{
    MergeByExpression(expr, vector<string>());
}

vector<list<var>> VariableOrderer::GetOrdered() const
{
    vector<pair<var, int>> pairList;
    for (auto const &v : vars) {
        auto varIndex = varIndices.find(v.first);
        auto p = pair<var, int>(v, unionFind->find(varIndex->second));
        pairList.push_back(p);
    }

    std::sort(
        pairList.begin(), pairList.end(),
        [](const std::pair<var, int> &left, const std::pair<var, int> &right) {
            return (left.second < right.second) ||
                   (left.second == right.second &&
                    left.first.second < right.first.second);
        });

    vector<list<var>> orderedVarGroups;

    list<var> currentGroup;
    int lastGroupIndex = 0;
    for (auto const &p : pairList) {
        if (p.second != lastGroupIndex) {
            if (currentGroup.size() > 0) {
                orderedVarGroups.push_back(currentGroup);
                currentGroup.clear();
            }
            lastGroupIndex = p.second;
        }
        currentGroup.push_back(p.first);
    }
    orderedVarGroups.push_back(currentGroup);

    std::sort(orderedVarGroups.begin(), orderedVarGroups.end(),
              [](const list<var> &left, const list<var> &right) {
                  return left.size() > right.size();
              });

    return orderedVarGroups;
}
