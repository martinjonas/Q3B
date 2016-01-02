#include "ExprToBDDTransformer.h"
#include <cmath>
#include <iostream>
#include <sstream>
#include <list>
#include <climits>
#include <algorithm>

#include "HexHelper.h"

#define DEBUG false

bdd constIteBdd;

bdd constThenElse(const bdd &a, const bdd &b)
{
    return bdd_ite(constIteBdd, a, b);
}

bddPair* pairToReplace;

bdd replacePair(const bdd &inputBdd)
{
    return bdd_replace(inputBdd, pairToReplace);
}

using namespace std;
using namespace z3;

ExprToBDDTransformer::ExprToBDDTransformer(z3::context &ctx, z3::expr e) : expression(e)
{    
  this->context = &ctx;      

  loadVars();
  setApproximationType(SIGN_EXTEND);
}

  void ExprToBDDTransformer::getVars(const z3::expr &e)
  {
      auto item = processedVarsCache.find((Z3_ast)e);
      if (item != processedVarsCache.end())
      {
          return;
      }

      if (e.is_app())
      {
          func_decl f = e.decl();
          unsigned num = e.num_args();

          if (num == 0 && f.name() != NULL)
          {
            z3::sort s = f.range();

            if (s.is_bv() && !e.is_numeral())
            {
              var c = make_pair(f.name().str(), s.bv_size());
              constSet.insert(c);
            }
            else if (s.is_bool())
            {
                stringstream ss;
                ss << e;
                var c = make_pair(ss.str(), 1);
                constSet.insert(c);
            }
          }
          else
          {
            for (unsigned i = 0; i < num; i++)
            {
              getVars(e.arg(i));
            }
          }
      }
      else if (e.is_const())
      {
        if (e.get_sort().is_bool())
        {
            stringstream ss;
            ss << e;

            if (ss.str() == "true" || ss.str() == "false")
            {
              return;
            }

            var c = make_pair(ss.str(), 1);
            constSet.insert(c);
        }
      }
      else if(e.is_quantifier())
      {
        Z3_ast ast = (Z3_ast)e;

        int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

        for (int i = 0; i < boundVariables; i++)
        {
            Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
            Z3_sort z3_sort = Z3_get_quantifier_bound_sort(*context, ast, i);

            symbol current_symbol(*context, z3_symbol);
            z3::sort current_sort(*context, z3_sort);

            if (current_sort.is_bool())
            {
                var c = make_pair(current_symbol.str(), 1);
                boundVarSet.insert(c);
            }
            else if (current_sort.is_bv())
            {
                var c = make_pair(current_symbol.str(), current_sort.bv_size());
                boundVarSet.insert(c);
            }
        }

        getVars(e.body());
      }

      processedVarsCache.insert((Z3_ast)e);
  }

  void ExprToBDDTransformer::loadVars()
  {            
    getVars(expression);
    processedVarsCache.clear();

    std::cout << "Bound vars: " << boundVarSet.size() << std::endl;

    set<var> allVars;
    allVars.insert(constSet.begin(), constSet.end());
    allVars.insert(boundVarSet.begin(), boundVarSet.end());

    if (allVars.size() == 0)
    {
        bdd_extvarnum(1);
        return;
    }

    VariableOrderer orderer(allVars, *context);
    orderer.OrderFor(expression);
    list<list<var>> orderedGroups = orderer.GetOrdered();

    int varCount = allVars.size();

    int maxBitSize = 0;
    for(auto const &v : allVars)
    {
        if (v.second > maxBitSize) maxBitSize = v.second;
    }

    bdd_extvarnum(varCount * maxBitSize);

    if (DEBUG)
    {
        cout << "Groups: " << orderedGroups.size() << endl;
    }

    int offset = 0;
    for(auto const &group : orderedGroups)
    {
      if (DEBUG)
      {
        cout << "Group size: " << group.size() << endl;
      }
      int i = 0;
      for (auto const &v : group)
      {
          int bitnum = v.second;
          bvec varBvec = bvec_var(bitnum, offset + i, group.size());
          vars[v.first] = varBvec;

          int indices[bitnum];
          int currentVar = offset + i;

          varIndices[v.first] = vector<int>();

          for (int bit = 0; bit <= bitnum; bit++)
          {
            indices[bit] = currentVar;
            varIndices[v.first].push_back(currentVar);
            currentVar += group.size();            
          }

          bdd varSet = bdd_makeset(indices, bitnum);
          varSets[v.first] = varSet;                    

          i++;
      }
      offset += maxBitSize * group.size();
    }
  }

  void ExprToBDDTransformer::loadBDDsFromExpr(expr e)
  {    
    bddExprCache.clear();
    bvecExprCache.clear();

    this->expression = e;
    m_bdd = getBDDFromExpr(e, vector<boundVar>());
  }

  bdd ExprToBDDTransformer::getConjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars)
  {
      vector<bdd> results;

      for (unsigned int i = 0; i < arguments.size(); i++)
      {
        bdd argBdd = getBDDFromExpr(arguments[i], boundVars);

        if (argBdd.id() == 0)
        {
            return bdd_false();
        }
        else
        {
            results.push_back(argBdd);
            if (DEBUG)
            {
                cout << bdd_nodecount(argBdd) << endl;
            }
        }
      }

      if (results.size() == 0)
      {
          return bdd_true();
      }
      else
      {
          std::sort(results.begin(), results.end(),
              [](const bdd& a, const bdd& b) -> bool
          {
              return bdd_nodecount(a) < bdd_nodecount(b);
          });

          bdd toReturn = results.at(0);

          for (unsigned int i = 1; i < results.size(); i++)
          {
              toReturn = bdd_and(toReturn, results.at(i));

              if (bdd_nodecount(toReturn) == 0)
              {
                  if (toReturn.id() == 0)
                  {
                    return bdd_false();
                  }
              }
          }

          return toReturn;
      }
  }

  bdd ExprToBDDTransformer::getDisjunctionBdd(const vector<expr> &arguments, const vector<boundVar> &boundVars)
  {
      vector<bdd> results;

      for (unsigned int i = 0; i < arguments.size(); i++)
      {
        bdd argBdd = getBDDFromExpr(arguments[i], boundVars);

        if (argBdd.id() == 1)
        {
            return bdd_true();
        }
        else
        {
            results.push_back(argBdd);

            if (DEBUG)
            {
                cout << bdd_nodecount(argBdd) << endl;
            }
        }
      }

      if (results.size() == 0)
      {
          return bdd_false();
      }
      else
      {
          std::sort(results.begin(), results.end(),
              [](const bdd& a, const bdd& b) -> bool
          {
              return bdd_nodecount(a) > bdd_nodecount(b);
          });

          bdd toReturn = results.at(0);

          for (unsigned int i = 1; i < results.size(); i++)
          {
              toReturn = bdd_or(toReturn, results.at(i));

              if (bdd_nodecount(toReturn) == 0)
              {
                  if (toReturn.id() == 1)
                  {
                    return bdd_true();
                  }
              }
          }

          return toReturn;
      }
  }

  bdd ExprToBDDTransformer::getBDDFromExpr(const expr &e, vector<boundVar> boundVars)
  {    
    assert(e.is_bool());
    //cout << e << endl;

    auto item = bddExprCache.find((Z3_ast)e);
    if (item != bddExprCache.end())
    {
        vector<boundVar> cachedBoundVars = (item->second).second;
        bool correctBoundVars = true;

        int pairsCount = min(boundVars.size(), cachedBoundVars.size());

        for (int i = 0; i < pairsCount; i++)
        {
            string oldVarName = cachedBoundVars[cachedBoundVars.size() - i - 1].first;
            string newVarName = boundVars[boundVars.size() - i - 1].first;

            if (oldVarName != newVarName)
            {
                correctBoundVars = false;
            }
        }

        if (correctBoundVars)
        {            
            return (item->second).first;
        }
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];
        return bvec_equ(vars[bVar.first], bvec_true(1));
    }
    else if (e.is_const())
    {
      //cout << "CONST: " << e << endl;
      stringstream ss;
      ss << e;
            
      if (ss.str() == "true")
      {
        return bdd_true();
      }
      else if (ss.str() == "false")
      {        
        return bdd_false();
      }      
            
      bdd toReturn = bvec_equ(vars[ss.str()], bvec_true(1));
      return toReturn;
    }
    else if (e.is_app())
    {
      //cout << "APP: " << e << endl;
      func_decl f = e.decl();
      unsigned num = e.num_args();

      string functionName = f.name().str();
      if (functionName == "=")
      {
        auto sort = e.arg(0).get_sort();
        bdd result;

        assert(sort.is_bv() || sort.is_bool());
        if (sort.is_bv())
        {
            auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
            auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
            result = bvec_equ(arg0, arg1);
        }
        else if (sort.is_bool())
        {
            auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
            auto arg1 = getBDDFromExpr(e.arg(1), boundVars);
            result = bdd_biimp(arg0, arg1);
        }

        return result;
      }
      else if (functionName == "not")
      {                        
        auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
        bdd result = bdd_not(arg0);

        return result;
      }
      else if (functionName == "and")
      {
        vector<expr> arguments;
        for (unsigned int i = 0; i < num; i++)
        {
            arguments.push_back(e.arg(i));
        }
        bdd result = getConjunctionBdd(arguments, boundVars);
        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "or")
      {
          vector<expr> arguments;
          for (unsigned int i = 0; i < num; i++)
          {
              arguments.push_back(e.arg(i));
          }
          bdd result = getDisjunctionBdd(arguments, boundVars);
          bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
          return result;
      }
      else if (functionName == "=>")
      {
        auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
        auto arg1 = getBDDFromExpr(e.arg(1), boundVars);
        bdd result =  bdd_imp(arg0, arg1);

        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvule")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        bdd result = bvec_lte(arg0, arg1);

        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvult")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        bdd result = bvec_lth(arg0, arg1);

        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvugr")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        bdd result = bvec_gte(arg0, arg1);

        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvugt")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        bdd result = bvec_gth(arg0, arg1);

        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvsle")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

        int size = e.arg(0).get_sort().bv_size();

        bdd head0 = arg0[size-1];
        bdd head1 = arg1[size-1];

        bvec tail0 = bvec_coerce(size - 1, arg0);
        bvec tail1 = bvec_coerce(size - 1, arg1);

        bdd differentSigns = bdd_and(bdd_biimp(head0, bdd_true()), bdd_biimp(head1, bdd_false()));

        bdd sameSigns = bdd_biimp(head0, head1);
        bdd sameSignsLte = bdd_and(sameSigns, bvec_lte(tail0, tail1));

        bdd result = bdd_or(differentSigns, sameSignsLte);
        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvslt")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

        int size = e.arg(0).get_sort().bv_size();

        bdd head0 = arg0[size-1];
        bdd head1 = arg1[size-1];

        bvec tail0 = bvec_coerce(size - 1, arg0);
        bvec tail1 = bvec_coerce(size - 1, arg1);

        bdd differentSigns = bdd_and(bdd_biimp(head0, bdd_true()), bdd_biimp(head1, bdd_false()));

        bdd sameSigns = bdd_biimp(head0, head1);
        bdd sameSignsLth = bdd_and(sameSigns, bvec_lth(tail0, tail1));

        bdd result = bdd_or(differentSigns, sameSignsLth);
        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "iff")
      {
        auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
        auto arg1 = getBDDFromExpr(e.arg(1), boundVars);
        bdd result = bdd_biimp(arg0, arg1);

        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "if")
      {
        auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
        auto arg1 = getBDDFromExpr(e.arg(1), boundVars);
        auto arg2 = getBDDFromExpr(e.arg(2), boundVars);
        bdd result = bdd_ite(arg0, arg1, arg2);

        bddExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else
      {
          cout << "function " << f.name().str() << endl;
      }
    }
    else if(e.is_quantifier())
    {
      Z3_ast ast = (Z3_ast)e;

      int boundVariables = Z3_get_quantifier_num_bound(*context, ast);

      for (int i = 0; i < boundVariables; i++)
      {
          Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
          //Z3_sort z3_sort = Z3_get_quantifier_bound_sort(*context, ast, i);

          symbol current_symbol(*context, z3_symbol);         

          string c = current_symbol.str();
          if (Z3_is_quantifier_forall(*context, ast))
          {
            boundVars.push_back(std::pair<string, BoundType>(c, UNIVERSAL));
          }
          else
          {
            boundVars.push_back(std::pair<string, BoundType>(c, EXISTENTIAL));
          }
      }

      bdd bodyBdd;
      if (!e.body().is_app() || (e.body().decl().decl_kind() != Z3_OP_OR && e.body().decl().decl_kind() != Z3_OP_AND))
      {
        bodyBdd = getBDDFromExpr(e.body(), boundVars);
      }

      for (int i = boundVariables - 1; i >= 0; i--)
      {
          Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
          symbol current_symbol(*context, z3_symbol);

          if (Z3_is_quantifier_forall(*context, ast))
          {              
              if (i == boundVariables - 1 && e.body().is_app() && (e.body().decl().decl_kind() == Z3_OP_OR || e.body().decl().decl_kind() == Z3_OP_AND))
              {
                  int numArgs = e.body().num_args();
                  std::vector<expr> leftHalf;
                  std::vector<expr> rightHalf;

                  for (int j = 0; j < numArgs; j++)
                  {
                      if (j < numArgs / 2)
                      {
                          leftHalf.push_back(e.body().arg(j));
                      }
                      else
                      {
                          rightHalf.push_back(e.body().arg(j));
                      }
                  }

                  if (e.body().decl().decl_kind() == Z3_OP_OR)
                  {
                    bodyBdd = bdd_appall(getDisjunctionBdd(leftHalf, boundVars),
                                       getDisjunctionBdd(rightHalf, boundVars),
                                       bddop_or,
                                       varSets[current_symbol.str()]);
                  }
                  else
                  {
                      bodyBdd = bdd_appall(getConjunctionBdd(leftHalf, boundVars),
                                         getConjunctionBdd(rightHalf, boundVars),
                                         bddop_and,
                                         varSets[current_symbol.str()]);
                  }
              }
              else
              {
                  bodyBdd = bdd_forall(bodyBdd, varSets[current_symbol.str()]);
              }
          }
          else
          {
              if (i == boundVariables - 1 && e.body().is_app() && (e.body().decl().decl_kind() == Z3_OP_OR || e.body().decl().decl_kind() == Z3_OP_AND))
              {
                  int numArgs = e.body().num_args();
                  std::vector<expr> leftHalf;
                  std::vector<expr> rightHalf;

                  for (int j = 0; j < numArgs; j++)
                  {
                      if (j < numArgs / 2)
                      {
                          leftHalf.push_back(e.body().arg(j));
                      }
                      else
                      {
                          rightHalf.push_back(e.body().arg(j));
                      }
                  }

                  if (e.body().decl().decl_kind() == Z3_OP_OR)
                  {
                    bodyBdd = bdd_appex(getDisjunctionBdd(leftHalf, boundVars),
                                       getDisjunctionBdd(rightHalf, boundVars),
                                       bddop_or,
                                       varSets[current_symbol.str()]);
                  }
                  else
                  {
                      bodyBdd = bdd_appex(getConjunctionBdd(leftHalf, boundVars),
                                         getConjunctionBdd(rightHalf, boundVars),
                                         bddop_and,
                                         varSets[current_symbol.str()]);
                  }
              }
              else
              {
                  bodyBdd = bdd_exist(bodyBdd, varSets[current_symbol.str()]);
              }
          }
      }

      bddExprCache.insert({(Z3_ast)e, {bodyBdd, boundVars}});
      return bodyBdd;
    }

    cout << "bdd else: " << e << endl;
    abort();
  }

  bvec ExprToBDDTransformer::getBvecFromExpr(const expr &e, vector<boundVar> boundVars)
  {    
    assert(e.is_bv());
    //cout << e << endl;

    auto item = bvecExprCache.find((Z3_ast)e);
    if (item != bvecExprCache.end())
    {
        vector<boundVar> cachedBoundVars = (item->second).second;
        bool correctBoundVars = true;

        int pairsCount = min(boundVars.size(), cachedBoundVars.size());

        for (int i = 0; i < pairsCount; i++)
        {
            string oldVarName = cachedBoundVars[cachedBoundVars.size() - i - 1].first;
            string newVarName = boundVars[boundVars.size() - i - 1].first;

            if (oldVarName != newVarName)
            {
                correctBoundVars = false;
            }
        }

        if (correctBoundVars)
        {            
            return (item->second).first;
        }
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);               
        boundVar bVar = boundVars[boundVars.size() - deBruijnIndex - 1];

        if (bVar.second == EXISTENTIAL && exisentialBitWidth != 0)
        {
            int bitSize = e.get_sort().bv_size();
            if (exisentialBitWidth > 0)
            {
                int newWidth = min(exisentialBitWidth, bitSize);                
                bvec var = vars[bVar.first];

                for (int i = newWidth; i < bitSize; i++)
                {
                    if (approximationType == ZERO_EXTEND)
                    {
                        var.set(i, bdd_false());
                    }
                    else if (approximationType == SIGN_EXTEND)
                    {
                        var.set(i, var[i - 1]);
                    }
                }

                return var;
            }
            else
            {
                int newWidth = min(-exisentialBitWidth, bitSize);
                bvec var = vars[bVar.first];

                for (int i = bitSize - newWidth - 1; i >= 0; i--)
                {
                    if (approximationType == ZERO_EXTEND)
                    {
                        var.set(i, bdd_false());
                    }
                    else if (approximationType == SIGN_EXTEND)
                    {
                        var.set(i, var[i + 1]);
                    }
                }

                return var;
            }
        }
        if (bVar.second == UNIVERSAL && universalBitWidth != 0)
        {
            int bitSize = e.get_sort().bv_size();
            if (universalBitWidth > 0)
            {
                int newWidth = min(universalBitWidth, bitSize);
                bvec var = vars[bVar.first];

                for (int i = newWidth; i < bitSize; i++)
                {
                    if (approximationType == ZERO_EXTEND)
                    {
                        var.set(i, bdd_false());
                    }
                    else if (approximationType == SIGN_EXTEND)
                    {
                        var.set(i, var[i - 1]);
                    }
                }

                return var;
            }
            else
            {
                int newWidth = min(-universalBitWidth, bitSize);
                bvec var = vars[bVar.first];

                for (int i = bitSize - newWidth - 1; i >= 0; i--)
                {
                    if (approximationType == ZERO_EXTEND)
                    {
                        var.set(i, bdd_false());
                    }
                    else if (approximationType == SIGN_EXTEND)
                    {
                        var.set(i, var[i + 1]);
                    }
                }

                return var;
            }
        }
        else
        {
            return vars[bVar.first];
        }
    }
    else if (e.is_numeral())
    {        
      return getNumeralBvec(e);
    }
    else if (e.is_const())
    {
      stringstream ss;
      ss << e;

      if (exisentialBitWidth != 0)
      {        
          int bitSize = e.get_sort().bv_size();
          if (exisentialBitWidth > 0)
          {
              int newWidth = min(exisentialBitWidth, bitSize);
              bvec var = vars[ss.str()];

              for (int i = newWidth; i < bitSize; i++)
              {
                  if (approximationType == ZERO_EXTEND)
                  {
                      var.set(i, bdd_false());
                  }
                  else if (approximationType == SIGN_EXTEND)
                  {
                      var.set(i, var[i - 1]);
                  }
              }

              return var;
          }
          else
          {
              int newWidth = min(-exisentialBitWidth, bitSize);
              bvec var = vars[ss.str()];

              for (int i = bitSize - newWidth - 1; i >= 0; i--)
              {
                  if (approximationType == ZERO_EXTEND)
                  {
                      var.set(i, bdd_false());
                  }
                  else if (approximationType == SIGN_EXTEND)
                  {
                      var.set(i, var[i + 1]);
                  }
              }

              return var;
          }
      }
      else
      {
        return vars[ss.str()];
      }
    }
    else if (e.is_app())
    {
      func_decl f = e.decl();
      unsigned num = e.num_args();

      string functionName = f.name().str();
      if (functionName == "bvadd")
      {
        bvec toReturn = getBvecFromExpr(e.arg(0), boundVars);
        for (unsigned int i = 1; i < num; i++)
        {
          toReturn = bvec_add(toReturn, getBvecFromExpr(e.arg(i), boundVars));
        }

        bvecExprCache.insert({(Z3_ast)e, {toReturn, boundVars}});
        return toReturn;
      }
      else if (functionName == "bvsub")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        bvec result = bvec_sub(arg0, arg1);

        bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvshl")
      {
        if (e.arg(1).is_numeral())
        {
          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          bvec result = bvec_shlfixed(arg0, getNumeralValue(e.arg(1)), bdd_false());

          bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
          return result;
        }
        else
        {
          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
          bvec result = bvec_shl(arg0, arg1, bdd_false());

          bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
          return result;
        }
      }
      else if (functionName == "bvlshr")
      {        
          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

          bvec arg0Reversed(arg0.bitnum());
          for (int i = 0; i < arg0.bitnum(); i++)
          {
            arg0Reversed.set(i, arg0[arg0.bitnum() - i - 1]);
          }

          bvec resultReversed = bvec_shl(arg0Reversed, arg1, bdd_false());

          bvec result(resultReversed.bitnum());
          for (int i = 0; i < resultReversed.bitnum(); i++)
          {
            result.set(i, resultReversed[resultReversed.bitnum() - i - 1]);
          }

          return result;
      }
      else if (functionName == "zero_extend")
      {
        Z3_func_decl z3decl = (Z3_func_decl)e.decl();
        int bitsExtend = Z3_get_decl_int_parameter(*context, z3decl, 0);

        int totalBits = bitsExtend + f.domain(0).bv_size();
        //cout << "EXTEND " << bitsExtend << " bits " << " to total " << totalBits << " bits " << endl;
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        bvec result = bvec_coerce(totalBits, arg0);

        return result;
      }
      else if (functionName == "concat")
      {
        int newSize = f.range().bv_size();
        int offset = 0;

        bvec currentBvec = bvec_false(newSize);
        assert(num > 0);
        for (int i = num-1; i >= 0; i--)
        {
          auto arg = getBvecFromExpr(e.arg(i), boundVars);          
          currentBvec = bvec_map2(currentBvec, 
              bvec_shlfixed(bvec_coerce(newSize, arg), offset, bdd_false()), bdd_xor);
          offset += f.domain(i).bv_size();
        }

        bvec result = currentBvec;
        return result;
      }
      else if (functionName == "extract")
      {
        Z3_func_decl z3decl = (Z3_func_decl)e.decl();

        int bitTo = Z3_get_decl_int_parameter(*context, z3decl, 0);
        int bitFrom = Z3_get_decl_int_parameter(*context, z3decl, 1);

        int extractBits = bitTo - bitFrom + 1;

        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        if (extractBits < 0)
        {
            cout << e << endl;
        }
        bvec result = bvec_coerce(extractBits, bvec_shrfixed(arg0, bitFrom, bdd_false()));

        bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvnot")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        bvec result = bvec_map1(arg0, bdd_not);

        return result;
      }
      else if (functionName == "bvor")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        bvec result = bvec_map2(arg0, arg1, bdd_or);

        bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvand")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        bvec result = bvec_map2(arg0, arg1, bdd_and);

        bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }
      else if (functionName == "bvxor")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        bvec result = bvec_map2(arg0, arg1, bdd_xor);

        bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
        return result;
      }      
      else if (functionName == "bvmul")
      {          
          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

          bvec result;
          if (arg0.bitnum() > 32 || arg1.bitnum() > 32 || (!bvec_isconst(arg0) && !bvec_isconst(arg1)))
          {
              auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
              auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

              int leftConstantCount = 0;
              int rightConstantCount = 0;

              for (unsigned int i = 0; i < e.arg(0).get_sort().bv_size(); i++)
              {
                if (arg0[i].id() < 2)
                {
                    leftConstantCount++;
                }

                if (arg1[i].id() < 2)
                {
                    rightConstantCount++;
                }
              }

              bvec result;
              if (leftConstantCount < rightConstantCount)
              {
                result = bvec_coerce(e.decl().range().bv_size(), bvec_mul(arg1, arg0));
                bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
                return result;
              }
              else
              {
                result = bvec_coerce(e.decl().range().bv_size(), bvec_mul(arg0, arg1));
                bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
                return result;
              }
          }

          if (bvec_isconst(arg1))
          {
              bvec tmp = arg0;
              arg0 = arg1;
              arg1 = tmp;
          }

          if (bvec_isconst(arg0))
          {
            unsigned int val = bvec_val(arg0);

            unsigned int largestDividingTwoPower = 0;
            for (int i = 0; i < 64; i++)
            {
                if (val % 2 == 0)
                {
                    largestDividingTwoPower++;
                    val = val >> 1;
                }
            }

            if (largestDividingTwoPower > 0)
            {
                result = bvec_shlfixed(bvec_mulfixed(arg1, val), largestDividingTwoPower, bdd_false());

                bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
                return result;
            }

            if (val > INT_MAX)
            {
                int leftConstantCount = 0;
                int rightConstantCount = 0;

                for (unsigned int i = 0; i < e.arg(0).get_sort().bv_size(); i++)
                {
                  if (arg0[i].id() < 2)
                  {
                      leftConstantCount++;
                  }

                  if (arg1[i].id() < 2)
                  {
                      rightConstantCount++;
                  }
                }

                if (leftConstantCount < rightConstantCount)
                {
                  result = bvec_coerce(e.decl().range().bv_size(), bvec_mul(arg1, arg0));
                  bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
                  return result;
                }
                else
                {
                  result = bvec_coerce(e.decl().range().bv_size(), bvec_mul(arg0, arg1));
                  bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
                  return result;
                }
            }
            result = bvec_mulfixed(arg1, val);

            bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
            return result;
          }
      }
      else if (functionName == "bvurem_i")
      {
          bvec div = bvec_false(e.decl().range().bv_size());
          bvec rem = bvec_false(e.decl().range().bv_size());

          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

          int result = bvec_div(arg0, arg1, div, rem);
          if (result == 0)
          {
              bvec result = rem;
              bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
              return result;
          }
          else
          {
              cout << "ERROR: division error" << endl;
              cout << "unknown";
              exit(0);
          }
      }
      else if (functionName == "bvudiv_i")
      {
          bvec div = bvec_false(e.decl().range().bv_size());
          bvec rem = bvec_false(e.decl().range().bv_size());

          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

          int result = bvec_div(arg0, arg1, div, rem);
          if (result == 0)
          {
              bvec result = div;
              bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
              return result;
          }
          else
          {
              cout << "ERROR: division error" << endl;
              cout << "unknown";
              exit(0);
          }
      }
      else if (functionName == "bvsdiv_i")
      {
          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

          int size = e.arg(0).get_sort().bv_size();

          bdd head0 = arg0[size-1];
          bdd head1 = arg1[size-1];

          bvec pp_div = bvec_false(e.decl().range().bv_size());
          bvec pp_rem = bvec_false(e.decl().range().bv_size());
          bvec_div(arg0, arg1, pp_div, pp_rem);

          bvec np_div = bvec_false(e.decl().range().bv_size());
          bvec np_rem = bvec_false(e.decl().range().bv_size());
          bvec_div(bvec_map1(arg0, bdd_not), arg1, np_div, np_rem);

          bvec pn_div = bvec_false(e.decl().range().bv_size());
          bvec pn_rem = bvec_false(e.decl().range().bv_size());
          bvec_div(arg0, bvec_map1(arg1, bdd_not), pn_div, pn_rem);

          bvec nn_div = bvec_false(e.decl().range().bv_size());
          bvec nn_rem = bvec_false(e.decl().range().bv_size());
          bvec_div(bvec_map1(arg0, bdd_not), bvec_map1(arg1, bdd_not), nn_div, nn_rem);

          bvec result = bvec_ite(
                      bdd_and(bdd_biimp(head0, bdd_false()), bdd_biimp(head1, bdd_false())),
                      pp_div,
                        bvec_ite(
                          bdd_and(bdd_biimp(head0, bdd_true()), bdd_biimp(head1, bdd_false())),
                          bvec_map1(np_div, bdd_not),
                            bvec_ite(
                              bdd_and(bdd_biimp(head0, bdd_false()), bdd_biimp(head1, bdd_true())),
                              bvec_map1(pn_div, bdd_not),
                              nn_div)));

          bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
          return result;
      }
      else if (functionName == "bvsrem_i")
      {
          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

          int size = e.arg(0).get_sort().bv_size();

          bdd head0 = arg0[size-1];
          bdd head1 = arg1[size-1];

          bvec pp_div = bvec_false(e.decl().range().bv_size());
          bvec pp_rem = bvec_false(e.decl().range().bv_size());
          bvec_div(arg0, arg1, pp_div, pp_rem);

          bvec np_div = bvec_false(e.decl().range().bv_size());
          bvec np_rem = bvec_false(e.decl().range().bv_size());
          bvec_div(bvec_map1(arg0, bdd_not), arg1, np_div, np_rem);

          bvec pn_div = bvec_false(e.decl().range().bv_size());
          bvec pn_rem = bvec_false(e.decl().range().bv_size());
          bvec_div(arg0, bvec_map1(arg1, bdd_not), pn_div, pn_rem);

          bvec nn_div = bvec_false(e.decl().range().bv_size());
          bvec nn_rem = bvec_false(e.decl().range().bv_size());
          bvec_div(bvec_map1(arg0, bdd_not), bvec_map1(arg1, bdd_not), nn_div, nn_rem);

          bvec result = bvec_ite(
                      bdd_and(bdd_biimp(head0, bdd_false()), bdd_biimp(head1, bdd_false())),
                      pp_rem,
                        bvec_ite(
                          bdd_and(bdd_biimp(head0, bdd_true()), bdd_biimp(head1, bdd_false())),
                          bvec_map1(np_rem, bdd_not),
                            bvec_ite(
                              bdd_and(bdd_biimp(head0, bdd_false()), bdd_biimp(head1, bdd_true())),
                              np_rem,
                              bvec_map1(nn_rem, bdd_not))));

          bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
          return result;
      }
      else if (functionName == "if")
      {
          auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
          auto arg2 = getBvecFromExpr(e.arg(2), boundVars);

          constIteBdd = arg0;
          bvec result = bvec_map2(arg1, arg2, constThenElse);

          bvecExprCache.insert({(Z3_ast)e, {result, boundVars}});
          return result;
      }
      else
      {
        //cout << "function " << f.name().str() << " expr " << e << endl;
        cout << "ERROR: not supported function " << functionName << endl;
        cout << "unknown";
        exit(0);
      }
    }

    cout << "bvec else" << e << endl;
    abort();
  }

  unsigned int ExprToBDDTransformer::getNumeralValue(const expr &e)
  {
      std::stringstream ss;
      ss << e;
      const string eString = ss.str();
      const string prefix = eString.substr(0, 2);
      const string valueString = eString.substr(2);

      ss.str("");      
      unsigned int value;

      if (prefix == "#x")
      {
        ss << std::hex << valueString;
        ss >> value;
      }
      else if (prefix == "#b")
      {
        value = stoull(valueString, 0, 2);
      }

      return value;
  }

  bvec ExprToBDDTransformer::getNumeralBvec(const z3::expr &e)
  {
      z3::sort s = e.get_sort();

      int value;
      Z3_bool success = Z3_get_numeral_int(*context, (Z3_ast)e, &value);

      if (false && success)
      {
        return bvec_con(s.bv_size(), value);
      }
      else
      {
        std::stringstream ss;
        ss << e;

        string numeralString = ss.str();

        int bitSize = s.bv_size();

        const string prefix = numeralString.substr(0, 2);
        string valueString = numeralString.substr(2);

        assert(prefix == "#x" || prefix == "#b");

        bvec toReturn(bitSize);
        if (prefix == "#x")
        {
            valueString = HexHelper::hex_str_to_bin_str(valueString);
        }

        int i = valueString.size();
        for (const char& c : valueString)
        {
          i--;
          if (c == '1')
          {
              toReturn.set(i, bdd_true());
          }
          else
          {
              toReturn.set(i, bdd_false());
          }
        }

        return toReturn;
      }
  }
  
  bdd ExprToBDDTransformer::Proccess()
  { 
    exisentialBitWidth = 0;
    universalBitWidth = 0;

    std::stringstream ss;
    ss << expression;
    if (ss.str() == "true")
    {
        std::cout << "Reason: simplification" << std::endl;
        return bdd_true();
    }
    else if (ss.str() == "false")
    {
        std::cout << "Reason: simplification" << std::endl;
        return bdd_false();
    }
    //cout << expression << endl;
    loadBDDsFromExpr(expression);    
    return m_bdd;
  }  

  bdd ExprToBDDTransformer::ProcessUnderapproximation(int bitWidth)
  {
      exisentialBitWidth = bitWidth;
      universalBitWidth = 0;

      loadBDDsFromExpr(expression);
      return m_bdd;
  }

  bdd ExprToBDDTransformer::ProcessOverapproximation(int bitWidth)
  {
      universalBitWidth = bitWidth;
      exisentialBitWidth = 0;

      loadBDDsFromExpr(expression);
      return m_bdd;
  }
