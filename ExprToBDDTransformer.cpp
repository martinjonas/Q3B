#include "ExprToBDDTransformer.h"
#include <cmath>
#include <iostream>
#include <sstream>
#include <list>
#include <climits>

#include "VariableOrderer.h"

bdd constIteBdd;

bdd constThenElse(const bdd &a, const bdd &b)
{
    return bdd_ite(constIteBdd, a, b);
}

using namespace std;
using namespace z3;

  set<var> ExprToBDDTransformer::getConsts(const expr &e) const
  {
    if (e.is_app())
    {
      func_decl f = e.decl();
      unsigned num = e.num_args();
      symbol name = f.name();
      string namestr = name.str();

      set<var> v;
      if (num == 0 && f.name() != NULL)
      {
        sort s = f.range();

        if (s.is_bv() && !e.is_numeral())
        {
          var c = make_pair(f.name().str(), s.bv_size());
          v.insert(c);
        }
      }
      else    
      {
        for (unsigned i = 0; i < num; i++)
        {
          set<var> consts = getConsts(e.arg(i));
          v.insert(consts.begin(), consts.end());
        }
      }

      return v;
    }
    else if(e.is_quantifier())  
    {
      Z3_ast ast = (Z3_ast)e;

      int boundVariables = Z3_get_quantifier_num_bound(*context, ast);
      cout << "BOUND: " << boundVariables << endl;

      //for (int i = 0; i < boundVariables; i++)
      //{
          //Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
          //Z3_sort z3_sort = Z3_get_quantifier_bound_sort(*context, ast, i);

          //symbol current_symbol(*context, z3_symbol);
          //sort current_sort(*context, z3_sort);
          //cout << current_symbol.str() << " -- bv " << current_sort.bv_size() << endl;
      //}

      //cout << e.num_args() << endl;
      return getConsts(e.body());
    }

    set<var> v;
    return v;
  }

  std::set<var> ExprToBDDTransformer::getBoundVars(const z3::expr &e) const
  {
      set<var> v;
      if (e.is_app())
      {
        unsigned num = e.num_args();

        if (num != 0)
        {
          for (unsigned i = 0; i < num; i++)
          {
            set<var> vars = getBoundVars(e.arg(i));
            v.insert(vars.begin(), vars.end());
          }
        }

        return v;
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
            sort current_sort(*context, z3_sort);

            var c;
            if (current_sort.is_bool())
            {
                var c = make_pair(current_symbol.str(), 1);
                v.insert(c);
            }
            else if (current_sort.is_bv())
            {
                var c = make_pair(current_symbol.str(), current_sort.bv_size());
                v.insert(c);
            }
        }

        set<var> vars = getBoundVars(e.body());
        v.insert(vars.begin(), vars.end());
      }

      return v;
  }

  void ExprToBDDTransformer::loadVars()
  {    
    set<var> consts = getConsts(expression);
    set<var> boundVars = getBoundVars (expression);

    set<var> allVars;
    allVars.insert(consts.begin(), consts.end());
    allVars.insert(boundVars.begin(), boundVars.end());

    VariableOrderer orderer(allVars, *context);
    orderer.OrderFor(expression);
    list<list<var>> orderedGroups = orderer.GetOrdered();

    int varCount = consts.size() + boundVars.size();

    int maxBitSize = 0;
    for(auto const &v : allVars)
    {
        if (v.second > maxBitSize) maxBitSize = v.second;
    }

    bdd_extvarnum(varCount * maxBitSize);

    cout << "Groups: " << orderedGroups.size() << endl;

    int offset = 0;
    for(auto const &group : orderedGroups)
    {
      cout << "Group size: " << group.size() << endl;
      int i = 0;
      for (auto const &v : group)
      {
          int bitnum = v.second;
          bvec varBvec = bvec_var(bitnum, offset + i, group.size());
          vars[v.first] = varBvec;

          int indices[bitnum];
          int currentVar = offset + i;
          for (int bit = 0; bit <= bitnum; bit++)
          {
            indices[bit] = currentVar;
            currentVar += group.size();
          }

          bdd varSet = bdd_makeset(indices, bitnum);
          varSets[v.first] = varSet;

          i++;
      }
      offset += maxBitSize * group.size();
    }
  }

  bvec ExprToBDDTransformer::allocBvec(int size)
  {
  }

  void ExprToBDDTransformer::loadBDDsFromExpr(expr e)
  {    
    this->expression = e;
    m_bdd = getBDDFromExpr(e, vector<string>());
  }

  bdd ExprToBDDTransformer::getBDDFromExpr(expr e, vector<string> boundVars)
  {    
    assert(e.is_bool());
    //cout << e << endl;

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        return bvec_equ(vars[boundVars[boundVars.size() - deBruijnIndex - 1]], bvec_true(1));
    }
    else if (e.is_const())
    {
      //cout << "CONST: " << e << endl;
      stringstream ss;
      ss << e;
      
      if (ss.str() == "true")
      {
        bdd_true();
      }
      else if (ss.str() == "false")
      {
        bdd_false();
      }      
      
      cout << "CONST " << e << endl;
      abort();
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
        //cout << "NOT: " << e << endl;
        auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
        return bdd_not(arg0);
      }
      else if (functionName == "and")
      {
        //cout << "AND: " << e << endl;
        bdd toReturn = getBDDFromExpr(e.arg(0), boundVars);
        for (int i = 1; i < num; i++)
        {
          cout << bdd_nodecount(toReturn) << endl;
          toReturn = bdd_and(toReturn, getBDDFromExpr(e.arg(i), boundVars));
        }

        return toReturn;
      }
      else if (functionName == "or")
      {
        //cout << "OR: " << e << endl;
        bdd toReturn = getBDDFromExpr(e.arg(0), boundVars);
        for (int i = 1; i < num; i++)
        {
          cout << bdd_nodecount(toReturn) << endl;
          toReturn = bdd_or(toReturn, getBDDFromExpr(e.arg(i), boundVars));
        }

        return toReturn;
      }
      else if (functionName == "=>")
      {
        //cout << "BVSLE: " << e << endl;
        auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
        auto arg1 = getBDDFromExpr(e.arg(1), boundVars);
        return bdd_imp(arg0, arg1);
      }
      else if (functionName == "bvule")
      {
        //cout << "BVSLE: " << e << endl;
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        return bvec_lte(arg0, arg1);
      }
      else if (functionName == "bvult")
      {
        //cout << "BVSLE: " << e << endl;
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        return bvec_lth(arg0, arg1);
      }
      else if (functionName == "bvugr")
      {
        //cout << "BVSLE: " << e << endl;
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        return bvec_gte(arg0, arg1);
      }
      else if (functionName == "bvugt")
      {
        //cout << "BVSLE: " << e << endl;
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        return bvec_gth(arg0, arg1);
      }
      else if (functionName == "bvsle")
      {
        //cout << "BVSLE: " << e << endl;
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

        int size = e.arg(0).get_sort().bv_size();

        bvec head0 = bvec_coerce(1, bvec_shrfixed(arg0, size - 1, bdd_false()));
        bvec head1 = bvec_coerce(1, bvec_shrfixed(arg1, size - 1, bdd_false()));

        bvec tail0 = bvec_coerce(size - 1, arg0);
        bvec tail1 = bvec_coerce(size - 1, arg1);

        bdd differentSigns = bdd_and(bvec_equ(head0, bvec_true(1)), bvec_equ(head1, bvec_false(1)));

        bdd sameSigns = bvec_equ(head0, head1);
        bdd bothPositive = bdd_and(sameSigns, bdd_and(bvec_equ(head0, bvec_false(1)), bvec_lte(tail0, tail1)));
        bdd bothNegative = bdd_and(sameSigns, bdd_and(bvec_equ(head0, bvec_true(1)), bvec_lte(tail1, tail0)));

        return bdd_or(differentSigns, bdd_or(bothPositive, bothNegative));
      }
      else if (functionName == "bvslt")
      {
        //cout << "BVSLE: " << e << endl;
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

        int size = e.arg(0).get_sort().bv_size();

        bvec head0 = bvec_coerce(1, bvec_shrfixed(arg0, size - 1, bdd_false()));
        bvec head1 = bvec_coerce(1, bvec_shrfixed(arg1, size - 1, bdd_false()));

        bvec tail0 = bvec_coerce(size - 1, arg0);
        bvec tail1 = bvec_coerce(size - 1, arg1);

        bdd differentSigns = bdd_and(bvec_equ(head0, bvec_true(1)), bvec_equ(head1, bvec_false(1)));

        bdd sameSigns = bvec_equ(head0, head1);
        bdd bothPositive = bdd_and(sameSigns, bdd_and(bvec_equ(head0, bvec_false(1)), bvec_lth(tail0, tail1)));
        bdd bothNegative = bdd_and(sameSigns, bdd_and(bvec_equ(head0, bvec_true(1)), bvec_lth(tail1, tail0)));

        return bdd_or(differentSigns, bdd_or(bothPositive, bothNegative));
      }
      else if (functionName == "iff")
      {
        //cout << "BVSLE: " << e << endl;
        auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
        auto arg1 = getBDDFromExpr(e.arg(1), boundVars);
        return bdd_biimp(arg0, arg1);
      }
      else if (functionName == "if")
      {
        //cout << "BVSLE: " << e << endl;
        auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
        auto arg1 = getBDDFromExpr(e.arg(1), boundVars);
        auto arg2 = getBDDFromExpr(e.arg(2), boundVars);
        return bdd_ite(arg0, arg1, arg2);
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
      //cout << "BOUND: " << boundVariables << endl;

      for (int i = 0; i < boundVariables; i++)
      {
          Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
          //Z3_sort z3_sort = Z3_get_quantifier_bound_sort(*context, ast, i);

          symbol current_symbol(*context, z3_symbol);
          //sort current_sort(*context, z3_sort);
          //cout << current_symbol.str() << " -- bv " << current_sort.bv_size() << endl;

          string c = current_symbol.str();
          boundVars.push_back(c);
      }

      bdd bodyBdd = getBDDFromExpr(e.body(), boundVars);

      for (int i = boundVariables - 1; i >= 0; i--)
      {
          Z3_symbol z3_symbol = Z3_get_quantifier_bound_name(*context, ast, i);
          //Z3_sort z3_sort = Z3_get_quantifier_bound_sort(*context, ast, i);

          symbol current_symbol(*context, z3_symbol);
          //sort current_sort(*context, z3_sort);
          //cout << current_symbol.str() << " -- bv " << current_sort.bv_size() << endl;

          if (Z3_is_quantifier_forall(*context, ast))
          {
              cout << "REMOVING UNIVERSAL: " << current_symbol.str() << endl;
              bodyBdd = bdd_forall(bodyBdd, varSets[current_symbol.str()]);
          }
          else
          {
              cout << "REMOVING EXISTENTIAL: " << current_symbol.str() << endl;
              bodyBdd = bdd_exist(bodyBdd, varSets[current_symbol.str()]);
          }
      }

      return bodyBdd;
    }

    cout << "bdd else: " << e << endl;
    abort();
  }

  bvec ExprToBDDTransformer::getBvecFromExpr(expr e, vector<string> boundVars)
  {
    if (!e.is_bv())
    {
        cout << e << endl;
        cout << e.get_sort() << endl;
    }
    assert(e.is_bv());

    //cout << e << endl;

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        auto v = vars[boundVars[boundVars.size() - deBruijnIndex - 1]];
        return v;
    }
    else if (e.is_numeral())
    {
      sort s = e.get_sort();
      int value = getNumeralValue(e);

      return bvec_con(s.bv_size(), value);
    }
    else if (e.is_const())
    {
      stringstream ss;
      ss << e;
      set<string> varSet {ss.str()};
      return vars[ss.str()];
    }
    else if (e.is_app())
    {
      func_decl f = e.decl();
      unsigned num = e.num_args();

      string functionName = f.name().str();
      if (functionName == "bvadd")
      {
        bvec toReturn = getBvecFromExpr(e.arg(0), boundVars);
        for (int i = 1; i < num; i++)
        {
          toReturn = bvec_add(toReturn, getBvecFromExpr(e.arg(i), boundVars));
        }

        return toReturn;
      }
      else if (functionName == "bvsub")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        return bvec_sub(arg0, arg1);
      }
      else if (functionName == "bvshl")
      {
        if (e.arg(1).is_numeral())
        {
          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          return bvec_shlfixed(arg0, getNumeralValue(e.arg(1)), bdd_false());
        }
        else
        {
          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
          return bvec_shl(arg0, arg1, bdd_false());
        }
      }
      else if (functionName == "zero_extend")
      {
        std::stringstream ss;
        ss << e;

        int bitsExtend;
        string temp;
        ss >> temp >> temp >> bitsExtend;

        int totalBits = bitsExtend + f.domain(0).bv_size();
        //cout << "EXTEND " << bitsExtend << " bits " << " to total " << totalBits << " bits " << endl;
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        return bvec_coerce(totalBits, arg0);
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

        return currentBvec;
      }
      else if (functionName == "extract")
      {
        std::stringstream ss;
        ss << e;

        int bitTo, bitFrom;
        string temp;
        ss >> temp >> temp >> bitTo >> bitFrom;

        int extractBits = bitTo - bitFrom + 1;

        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        return bvec_coerce(extractBits, bvec_shrfixed(arg0, bitFrom, bdd_false()));
      }
      else if (functionName == "bvnot")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        return bvec_map1(arg0, bdd_not);
      }
      else if (functionName == "bvor")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        return bvec_map2(arg0, arg1, bdd_or);
      }
      else if (functionName == "bvand")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        return bvec_map2(arg0, arg1, bdd_and);
      }
      else if (functionName == "bvxor")
      {
        auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
        auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
        return bvec_map2(arg0, arg1, bdd_xor);
      }      
      else if (functionName == "bvmul")
      {
          //cout << e << endl;
          if (!e.arg(0).is_const() && !e.arg(1).is_const())
          {
              cout << "ERROR: non-linear multiplication not supported" << endl;
              cout << "unknown";
              exit(0);
          }

          auto arg0 = getBvecFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);

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
                //cout << e << endl;
                //cout << "power: " << largestDividingTwoPower << ", mult: " << val << endl;
                bvec ret = bvec_shlfixed(bvec_mulfixed(arg1, val), largestDividingTwoPower, bdd_false());
                //cout << "done" << endl;
                return ret;
            }

            if (val > INT_MAX)
            {
                cout << "ERROR: multiplication by too large constant" << e.arg(0) << endl;
                cout << "unknown";
                exit(0);
            }
            return bvec_mulfixed(arg1, val);
          }
          else if (bvec_isconst(arg1))
          {
            unsigned int val = bvec_val(arg1);
            if (val > INT_MAX)
            {
                cout << "ERROR: multiplication by too large constant" << e.arg(1) << endl;
                cout << "unknown";
                exit(0);
            }
            return bvec_mulfixed(arg0, val);
          }          
      }
      else if (functionName == "bvsdiv_i")
      {
          cout << "ERROR: division not supported" << endl;
          cout << "unknown";
          exit(0);
      }
      else if (functionName == "if")
      {
          auto arg0 = getBDDFromExpr(e.arg(0), boundVars);
          auto arg1 = getBvecFromExpr(e.arg(1), boundVars);
          auto arg2 = getBvecFromExpr(e.arg(2), boundVars);

          constIteBdd = arg0;
          return bvec_map2(arg1, arg2, constThenElse);
      }
      else
      {
        //cout << "function " << f.name().str() << " expr " << e << endl;
        cout << "ERROR: not supported function " << functionName << endl;
        cout << "unknown";
        exit(0);
      }
    }

    //cout << "bvec else" << e << endl;
    abort();
  }

  int ExprToBDDTransformer::getNumeralValue(const expr e)
  {
      std::stringstream ss;
      ss << e;
      const string eString = ss.str();
      const string prefix = eString.substr(0, 2);
      const string valueString = eString.substr(2);

      ss.str("");      
      unsigned int value;

      if (eString.substr(0, 2) == "#x")
      {
        ss << std::hex << valueString;
        ss >> value;
      }
      else if (eString.substr(0, 2) == "#b")
      {
        value = stoull(valueString, 0, 2);
      }

      return value;
  }

  void ExprToBDDTransformer::PrintVars()
  {
    for(auto const &v : vars)
    {
      bvec bitvector = v.second;
      cout << v.first << " -> " << v.second << endl;
    }
  }
  
  bdd ExprToBDDTransformer::Proccess()
  { 
    //cout << expression << endl;
    loadBDDsFromExpr(expression);
    return m_bdd;
    //bdd_fnprintdot("bdd.dot", m_bdd);
  }
