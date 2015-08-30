#include "VariableOrderer.h"
#include <algorithm>

using namespace std;
using namespace z3;

VariableOrderer::VariableOrderer(const std::set<var> &vars, z3::context &ctx) : vars(vars)
{
    this->context = &ctx;
    this->unionFind = new UF(vars.size());

    int i = 0;
    for (auto const &v : vars)
    {
        varIndices[v.first] = i;
        i++;
    }
}

void VariableOrderer::MergeByExpression(const z3::expr &e, std::vector<std::string> boundVars)
{
    auto item = processedMergedSubformulaCache.find((Z3_ast)e);
    if (item != processedMergedSubformulaCache.end() && item->second == boundVars)
    {
        return;
    }

    assert(e.is_bool());

    if (e.is_app())
    {
      //cout << "APP: " << e << endl;
      func_decl f = e.decl();
      unsigned num = e.num_args();

      string functionName = f.name().str();
      //cout << "fun: " << functionName << endl;
      if (functionName == "not")
      {
        MergeByExpression(e.arg(0), boundVars);
      }
      else if (functionName == "and")
      {
        for (unsigned int i = 0; i < num; i++)
        {
          MergeByExpression(e.arg(i), boundVars);
        }
      }
      else if (functionName == "or")
      {
          for (unsigned int i = 0; i < num; i++)
          {
            MergeByExpression(e.arg(i), boundVars);
          }
      }
      else if (functionName == "iff")
      {
         MergeByExpression(e.arg(0), boundVars);
         MergeByExpression(e.arg(1), boundVars);
      }
      else if (functionName == "if")
      {
         MergeByExpression(e.arg(0), boundVars);
         MergeByExpression(e.arg(1), boundVars);
         MergeByExpression(e.arg(2), boundVars);
      }
      else
      {
          std::set<std::string> vars;
          for (unsigned int i = 0; i < num; i++)
          {
            set<std::string> currentVars = GetVars(e.arg(i), boundVars);
            vars.insert(currentVars.begin(), currentVars.end());
          }

          if (vars.size() > 0)
          {
            for (auto const &v : vars)
            {
                MarkDependent(*vars.begin(), v);
            }
          }
          //cout << "function " << f.name().str() << endl;
      }
    }
    else if(e.is_quantifier())
    {
      Z3_ast ast = (Z3_ast)e;

      int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

      for (int i = 0; i < boundVariables; i++)
      {
          Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);

          symbol current_symbol(*context, z3_symbol);

          string c = current_symbol.str();
          boundVars.push_back(c);
      }

      MergeByExpression(e.body(), boundVars);
      //bdd bodyBdd = getBDDFromExpr(e.body(), boundVars);
    }

    processedMergedSubformulaCache.insert({(Z3_ast)e, boundVars});
}

set<string> VariableOrderer::GetVars(const expr &e, std::vector<std::string> boundVars)
{    
    set<string> vars;

    auto item = processedVarsCache.find((Z3_ast)e);
    if (item != processedVarsCache.end() && item->second == boundVars)
    {
        return vars;
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        vars.insert(boundVars[boundVars.size() - deBruijnIndex - 1]);
        return vars;
    }
    if (e.is_app())
    {
      func_decl f = e.decl();
      unsigned num = e.num_args();

      if (num != 0)
      {
        for (unsigned i = 0; i < num; i++)
        {
          set<string> currentVars = GetVars(e.arg(i), boundVars);
          vars.insert(currentVars.begin(), currentVars.end());

          processedVarsCache.insert({(Z3_ast)e.arg(i), boundVars});
        }
      }
      else if (f.name() != NULL)
      {
        z3::sort s = f.range();

        if (s.is_bv() && !e.is_numeral())
        {
          vars.insert(f.name().str());
        }
      }

      return vars;
    }
    else if(e.is_quantifier())
    {
      Z3_ast ast = (Z3_ast)e;

      int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

      for (int i = 0; i < boundVariables; i++)
      {
          Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);

          symbol current_symbol(*context, z3_symbol);

          string c = current_symbol.str();
          boundVars.push_back(c);
      }

      return GetVars(e.body(), boundVars);
      //bdd bodyBdd = getBDDFromExpr(e.body(), boundVars);
    }

    return vars;    
}

void VariableOrderer::MarkDependent(const string &x, const string &y)
{
    int index1 = varIndices[x];
    int index2 = varIndices[y];
    unionFind->merge(index1, index2);
    //cout << "merging " << x << " " << y << endl;
}

void VariableOrderer::OrderFor(const z3::expr &expr)
{
    cout << "OrderFor" << std::endl;
    MergeByExpression(expr, vector<string>());
}

list<list<var>> VariableOrderer::GetOrdered() const
{
    vector<pair<var, int>> pairList;
    for (auto const &v : vars)
    {
        auto varIndex = varIndices.find(v.first);
        auto p = pair<var, int>(v, unionFind->find(varIndex->second));
        pairList.push_back(p);
    }

    std::sort(pairList.begin(), pairList.end(), [](const std::pair<var,int> &left, const std::pair<var,int> &right) {
        return left.second < right.second;
    });

    list<list<var>> orderedVarGroups;

    list<var> currentGroup;
    int lastGroupIndex = 0;
    for (auto const &p : pairList)
    {
        if (p.second != lastGroupIndex)
        {
            if (currentGroup.size() > 0)
            {
              orderedVarGroups.push_back(currentGroup);
              currentGroup.clear();
            }
            lastGroupIndex = p.second;
        }
        currentGroup.push_back(p.first);
    }
    orderedVarGroups.push_back(currentGroup);
    return orderedVarGroups;
}
