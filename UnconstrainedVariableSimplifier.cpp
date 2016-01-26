#include "UnconstrainedVariableSimplifier.h"

using namespace std;
using namespace z3;

map<string, int> UnconstrainedVariableSimplifier::countVariableOccurences(z3::expr e, vector<string> boundVars)
{
    map<string, int> varCounts;

    auto item = subformulaVariableCounts.find((Z3_ast)e);
    if (item != subformulaVariableCounts.end() && (item->second).second == boundVars)
    {
        return (item->second).first;
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        varCounts[boundVars[boundVars.size() - deBruijnIndex - 1]] = 1;
        return varCounts;
    }
    if (e.is_app())
    {
      func_decl f = e.decl();
      unsigned num = e.num_args();

      if (num != 0)
      {
        for (unsigned i = 0; i < num; i++)
        {
            auto currentVarCounts = countVariableOccurences(e.arg(i), boundVars);

            for (auto &item : currentVarCounts)
            {
                auto singleVarCount = varCounts.find(item.first);
                if (singleVarCount == varCounts.end())
                {
                    varCounts[item.first] = item.second;
                }
                else
                {
                    varCounts[item.first] = singleVarCount->second + item.second;
                }
            }
        }
      }
      else if (f.name() != NULL)
      {
        z3::sort s = f.range();

        if (s.is_bv() && !e.is_numeral())
        {
            varCounts[f.name().str()] = 1;
        }
      }

      subformulaVariableCounts.insert({(Z3_ast)e, {varCounts, boundVars}});
      return varCounts;
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

      auto result = countVariableOccurences(e.body(), boundVars);
      subformulaVariableCounts.insert({(Z3_ast)e, {result, boundVars}});
      return result;
    }

    return varCounts;
}

void UnconstrainedVariableSimplifier::SimplifyIte()
{
    unsigned oldHash = 0;

    //expression = expression.simplify();
    //expression = ApplyConstantEqualities(expression);

    while (oldHash != expression.hash())
    {
        oldHash = expression.hash();

        SimplifyOnce();
    }
}

z3::expr UnconstrainedVariableSimplifier::simplifyOnce(expr e, std::vector<pair<string, BoundType>> boundVars, bool isPositive = true)
{
    auto item = simplificationCache.find((Z3_ast)e);
    if (item != simplificationCache.end() && (item->second).second == boundVars)
    {
        return (item->second).first;
    }

    if (e.is_app())
    {
        func_decl f = e.decl();
        unsigned num = e.num_args();
        string name = f.name().str();

        if (name == "bvadd" && num == 2)
        {
            if (isVar(e.arg(0)) && isVar(e.arg(1)))
            {
                if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0)))
                {
                    return e.arg(0);
                }
                else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1)))
                {
                    return e.arg(1);
                }
            }
        }
        else if (name == "bvnot")
        {
            if (isUnconstrained(e.arg(0), boundVars))
            {
                return e.arg(0);
            }
        }
        else if (name == "bvand" || name == "bvor" || name == "bvxor" || name == "bvmul")
        {
            if (isUnconstrained(e.arg(0), boundVars) && isUnconstrained(e.arg(1), boundVars))
            {
                if (isBefore(e.arg(0), e.arg(1)))
                {
                    return e.arg(1);
                }
                else
                {
                    return e.arg(0);
                }
            }
        }
        else if (name == "=")
        {
            if (isUnconstrained(e.arg(0), boundVars) && (isVar(e.arg(1)) || e.arg(1).is_numeral() || e.arg(1).is_const()))
            {
                if (e.arg(1).is_const())
                {
                    auto boundType = getBoundType(e.arg(0), boundVars);
                    if (boundType == EXISTENTIAL)
                    {
                        return isPositive ? context->bool_val(true) : context->bool_val(false);
                    }
                    else
                    {
                        return isPositive ? context->bool_val(false) : context->bool_val(true);
                    }
                }
            }
            else if (isUnconstrained(e.arg(1), boundVars) && (isVar(e.arg(0)) || e.arg(1).is_numeral() || e.arg(0).is_const()))
            {
                if (e.arg(0).is_const())
                {
                    auto boundType = getBoundType(e.arg(1), boundVars);
                    if (boundType == EXISTENTIAL)
                    {
                        return isPositive ? context->bool_val(true) : context->bool_val(false);
                    }
                    else
                    {
                        return isPositive ? context->bool_val(false) : context->bool_val(true);
                    }
                }
            }
            else if (isUnconstrained(e.arg(0), boundVars) && isUnconstrained(e.arg(1), boundVars))
            {
                BoundType boundType;
                if (isBefore(e.arg(0), e.arg(1)))
                {
                    boundType = getBoundType(e.arg(1), boundVars);
                }
                else
                {
                    boundType = getBoundType(e.arg(0), boundVars);
                }

                if (boundType == EXISTENTIAL)
                {
                    return isPositive ? context->bool_val(true) : context->bool_val(false);
                }
                else
                {
                    return isPositive ? context->bool_val(false) : context->bool_val(true);
                }
            }
        }

        if (num == 2)
        {
            if (isUnconstrained(e.arg(0), boundVars))
            {
                //std::cout << "unconstrained " << name << " (0)" << std::endl;
            }
            else if (isUnconstrained(e.arg(1), boundVars))
            {
                //std::cout << "unconstrained " << name << " (1)" << std::endl;
            }
        }

        expr_vector arguments(*context);
        for (int i = 0; i < num; i++)
        {
            if (name == "not")
            {
                arguments.push_back(simplifyOnce(e.arg(i), boundVars, !isPositive));
            }
            else
            {
                arguments.push_back(simplifyOnce(e.arg(i), boundVars, isPositive));
            }
        }

        auto result = f(arguments);
        simplificationCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);
        BoundType boundType = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;

        for (int i = 0; i < numBound; i++)
        {
            Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);

            symbol current_symbol(*context, z3_symbol);

            boundVars.push_back(make_pair(current_symbol.str(), boundType));
        }

        Z3_sort sorts [numBound];
        Z3_symbol decl_names [numBound];
        for (int i = 0; i < numBound; i++)
        {
            sorts[i] = Z3_get_quantifier_bound_sort(*context, ast, i);
            decl_names[i] = Z3_get_quantifier_bound_name(*context, ast, i);
        }

        Z3_ast quantAst = Z3_mk_quantifier(
                    *context,
                    Z3_is_quantifier_forall(*context, ast),
                    Z3_get_quantifier_weight(*context, ast),
                    0,
                    {},
                    numBound,
                    sorts,
                    decl_names,
                    (Z3_ast)simplifyOnce(e.body(), boundVars, isPositive));
        auto result = to_expr(*context, quantAst);
        return result;
    }

    simplificationCache.insert({(Z3_ast)e, {e, boundVars}});
    return e;
}

bool UnconstrainedVariableSimplifier::isUnconstrained(expr e, vector<pair<string, BoundType>> &boundVars)
{
    if (!isVar(e))
    {
        return false;
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        return (variableCounts[boundVars[boundVars.size() - deBruijnIndex - 1].first] == 1);
    }
    else if (e.is_app())
    {
      func_decl f = e.decl();
      unsigned num = e.num_args();

      if (num == 0 && f.name() != NULL)
      {
        return (variableCounts[f.name().str()] == 1);
      }
    }

    return false;
}

bool UnconstrainedVariableSimplifier::isVar(expr e)
{
    if (e.is_var())
    {
        return true;
    }
    else if (e.is_app() || e.is_numeral())
    {
      func_decl f = e.decl();
      unsigned num = e.num_args();

      if (num == 0 && f.name() != NULL)
      {
        return true;
      }
    }

    return false;
}

bool UnconstrainedVariableSimplifier::isBefore(expr a, expr b)
{
    if (a.is_var() && b.is_var())
    {
        Z3_ast astA = (Z3_ast)a;
        Z3_ast astB = (Z3_ast)b;
        int deBruijnIndexA = Z3_get_index_value(*context, astA);
        int deBruijnIndexB = Z3_get_index_value(*context, astB);

        return deBruijnIndexA > deBruijnIndexB;
    }
    else if (a.is_app())
    {
        return false;
    }
    else
    {
        return true;
    }
}

BoundType UnconstrainedVariableSimplifier::getBoundType(expr e, std::vector<std::pair<string, BoundType>> &boundVars)
{
    assert(isVar(e));

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        return boundVars[boundVars.size() - deBruijnIndex - 1].second;
    }
    else if (e.is_app())
    {
      func_decl f = e.decl();
      unsigned num = e.num_args();

      if (num == 0 && f.name() != NULL)
      {
        return EXISTENTIAL;
      }
    }

    assert(false);
}
