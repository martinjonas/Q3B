#include "UnconstrainedVariableSimplifier.h"
#include "ExprSimplifier.h"
#include <fstream>

using namespace std;
using namespace z3;

pair<map<string, int>, int> UnconstrainedVariableSimplifier::countVariableOccurences(z3::expr e, vector<string> boundVars)
{
    map<string, int> varCounts;

    auto item = subformulaVariableCounts.find((Z3_ast)e);
    if (item != subformulaVariableCounts.end() && (item->second).second == boundVars)
    {
        return {(item->second).first, subformulaMaxDeBruijnIndices[(Z3_ast)e]};
    }

    if (e.is_var())
    {
        Z3_ast ast = (Z3_ast)e;
        int deBruijnIndex = Z3_get_index_value(*context, ast);
        varCounts[boundVars[boundVars.size() - deBruijnIndex - 1]] = 1;
        return {varCounts, deBruijnIndex};
    }
	else if (e.is_const() && !e.is_numeral())
	{
        if (e.get_sort().is_bool())
        {
            stringstream ss;
            ss << e;

            if (ss.str() == "true" || ss.str() == "false")
            {
				return {varCounts, -1};
            }

			varCounts[ss.str()] = 1;
        }
        else if (e.get_sort().is_bv())
        {
            stringstream ss;
            ss << e;

			varCounts[ss.str()] = 1;
        }

		return {varCounts, -1};
	}
    else if (e.is_app())
    {      
		func_decl f = e.decl();
		unsigned num = e.num_args();

		int maxDeBruijnIndex = -1;

		if (num != 0)
		{
			for (unsigned i = 0; i < num; i++)
			{
				auto currentVarCounts = countVariableOccurences(e.arg(i), boundVars);
				
				for (auto &item : currentVarCounts.first)
				{
					auto singleVarCount = varCounts.find(item.first);
					if (singleVarCount == varCounts.end())
					{
						varCounts[item.first] = item.second;
					}
					else
					{
						if (singleVarCount->second + item.second > 1)
						{
							varCounts[item.first] = 2;		
						}
						else
						{
							varCounts[item.first] = singleVarCount->second + item.second;
						}
					}
				}

				if (currentVarCounts.second > maxDeBruijnIndex)
				{
					maxDeBruijnIndex = currentVarCounts.second;
				}
			}
		}
		else if (f.name() != NULL)
		{
			z3::sort s = f.range();

			if (s.is_bv() && !e.is_numeral())
			{
				stringstream ss;
				ss << e;
				varCounts[ss.str()] = 1;
			}
			else if (s.is_bool())
            {
				stringstream ss;
				ss << e;
				varCounts[ss.str()] = 1;
            }
		}

		subformulaVariableCounts.insert({(Z3_ast)e, {varCounts, boundVars}});
		subformulaMaxDeBruijnIndices.insert({(Z3_ast)e, maxDeBruijnIndex});
		return {varCounts, maxDeBruijnIndex};
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
		subformulaVariableCounts.insert({(Z3_ast)e, {result.first, boundVars}});
		subformulaMaxDeBruijnIndices.insert({(Z3_ast)e, result.second});
		return result;
    }
	
	assert(false);
    return {varCounts, -1};
}

void UnconstrainedVariableSimplifier::SimplifyIte()
{
    unsigned oldHash = 0;

    //expression = expression.simplify();
    //expression = ApplyConstantEqualities(expression);    

    int i = 0;

	ExprSimplifier simplifier(*context);
	
    while (oldHash != expression.hash())
    {
		//std::cout << expression << std::endl;
		oldHash = expression.hash();
      
		SimplifyOnce();
		//expression = simplifier.PushNegations(expression);
      
		subformulaVariableCounts.clear();
		subformulaMaxDeBruijnIndices.clear();
		variableCounts = countVariableOccurences(expression, std::vector<std::string>()).first;
		trueSimplificationCache.clear();      
		falseSimplificationCache.clear();      
      
		i++;
    }
}

z3::expr UnconstrainedVariableSimplifier::simplifyOnce(expr e, std::vector<pair<string, BoundType>> boundVars, bool isPositive = true)
{
    cacheMapType::iterator item;

    if (isPositive)
    {
      item = trueSimplificationCache.find((Z3_ast)e);
    }
    else
    {
      item = falseSimplificationCache.find((Z3_ast)e);
    }

    if ((isPositive && item != trueSimplificationCache.end()) || (!isPositive && item != falseSimplificationCache.end()))
    {
        auto cachedBoundVars =  (item->second).second;
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
	
    if (e.is_app())
    {
        func_decl f = e.decl();
        unsigned num = e.num_args();
        auto decl_kind = f.decl_kind();

        if (decl_kind == Z3_OP_BADD && num == 2)
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
        else if (decl_kind == Z3_OP_BNOT)
        {
            if (isUnconstrained(e.arg(0), boundVars))
            {
                return e.arg(0);
            }
        }
        else if (decl_kind == Z3_OP_BAND || decl_kind == Z3_OP_BOR || decl_kind == Z3_OP_BXOR)
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
		else if (decl_kind == Z3_OP_BMUL && num == 2)
        {
			bool unconstrained0 = isUnconstrained(e.arg(0), boundVars);
			bool unconstrained1 = isUnconstrained(e.arg(1), boundVars);
			
            if (unconstrained0 && unconstrained1)
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
			else if (unconstrained0 && e.arg(1).is_numeral())				
			{
				int zeroes = getNumberOfLeadingZeroes(e.arg(1));

				Z3_ast returnAst = Z3_mk_bvshl(*context, (Z3_ast)e.arg(0), (Z3_ast)(context->bv_val(zeroes, e.arg(0).get_sort().bv_size())));
				return to_expr(*context, returnAst);
			}
			else if (unconstrained1 && e.arg(0).is_numeral())				
			{
				int zeroes = getNumberOfLeadingZeroes(e.arg(0));

				Z3_ast returnAst = Z3_mk_bvshl(*context, (Z3_ast)e.arg(1), (Z3_ast)(context->bv_val(zeroes, e.arg(1).get_sort().bv_size())));
				return to_expr(*context, returnAst);
			}
			else if (unconstrained0)
			{
				expr arg1 = simplifyOnce(e.arg(1), boundVars, isPositive);

				int bvSize = e.arg(0).get_sort().bv_size();
				expr returnExpr = e.arg(0);

				for (int i = bvSize - 1; i >= 0; i--)
				{
					Z3_ast shiftAst = Z3_mk_bvshl(*context, (Z3_ast)arg1, (Z3_ast)(context->bv_val(i, e.arg(1).get_sort().bv_size())));
					returnExpr = ite(arg1.extract(i,i) != 0, to_expr(*context, shiftAst), returnExpr);
				}

				return returnExpr;
			}
			else if (unconstrained1)
			{
				expr arg0 = simplifyOnce(e.arg(0), boundVars, isPositive);

				int bvSize = e.arg(1).get_sort().bv_size();
				expr returnExpr = e.arg(1);

				for (int i = bvSize - 1; i >= 0; i--)
				{
					Z3_ast shiftAst = Z3_mk_bvshl(*context, (Z3_ast)arg0, (Z3_ast)(context->bv_val(i, e.arg(0).get_sort().bv_size())));
					returnExpr = ite(arg0.extract(i,i) != 0, to_expr(*context, shiftAst), returnExpr);
				}

				return returnExpr;
			}			
        }
		else if (decl_kind == Z3_OP_OR && num == 2)
		{
            if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0)))
            {
				std::cout << "unconstrained" << e << std::endl;
                auto boundType = getBoundType(e.arg(0), boundVars);
                if (boundType == EXISTENTIAL)
                {
                    return isPositive ? context->bool_val(true) : e.arg(1);
                }
                else
                {
                    return e.arg(1);
                }
            }
            else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1)))
            {
				std::cout << "unconstrained" << e << std::endl;
				auto boundType = getBoundType(e.arg(0), boundVars);
                if (boundType == EXISTENTIAL)
                {
                    return isPositive ? context->bool_val(true) : e.arg(0);
                }
                else
                {
					return e.arg(0);
                }
            }
		}
		else if (decl_kind == Z3_OP_AND && num == 2)
		{
            if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0)))
            {
				std::cout << "unconstrained" << e << std::endl;				
                auto boundType = getBoundType(e.arg(0), boundVars);
                if (boundType == EXISTENTIAL)
                {
                    return isPositive ? e.arg(1) : context->bool_val(false);
                }
                else
                {
                    return context->bool_val(false);
                }
            }
            else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1)))
            {
				std::cout << "unconstrained" << e << std::endl;				
				auto boundType = getBoundType(e.arg(0), boundVars);
                if (boundType == EXISTENTIAL)
                {
                    return isPositive ? e.arg(1) : context->bool_val(false);
                }
                else
                {
                    return context->bool_val(false);
                }
            }
		}		
		else if (decl_kind == Z3_OP_IFF)
		{
			return e;
//			return ((simplifyOnce(e.arg(0), boundVars, isPositive) || !simplifyOnce(e.arg(1), boundVars, !isPositive)) &&
//					(!simplifyOnce(e.arg(0), boundVars, !isPositive) || simplifyOnce(e.arg(1), boundVars, isPositive)));
		}
		else if (decl_kind == Z3_OP_NOT)
		{
			if (isUnconstrained(e.arg(0), boundVars))
			{
				return e.arg(0);
			}
		}
        else if (decl_kind == Z3_OP_EQ)
        {		
            if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0)))
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
            else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1)))
            {
				auto boundType = getBoundType(e.arg(1), boundVars);
				std::cout << "Bound type: " << boundType << std::endl;
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
        else if (decl_kind == Z3_OP_SLEQ)
        {
            if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0)))
            {
                auto boundType = getBoundType(e.arg(0), boundVars);
				auto bvSize = e.arg(1).get_sort().bv_size();                    
				
                if (boundType == EXISTENTIAL)
                {
                    if (isPositive)
                    {
						return context->bool_val(true);
                    }
                    else
                    {
						return !(e.arg(1) == concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1)));
                    }
                }
                else
                {
					return e.arg(1) == concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1));
                }
            }
            else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1)))
            {				
                auto boundType = getBoundType(e.arg(1), boundVars);
				auto bvSize = e.arg(1).get_sort().bv_size();
				
                if (boundType == EXISTENTIAL)
                {
                    if (isPositive)
                    {
						return context->bool_val(true);
                    }
                    else
                    {
						return !(e.arg(0) == concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)));
                    }
                }
                else
                {
					return e.arg(0) == concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1));
                }
            }
        }
		else if (decl_kind == Z3_OP_SLT)
        {
            if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0)))
            {
                auto boundType = getBoundType(e.arg(0), boundVars);
                if (boundType == EXISTENTIAL)
                {
                    auto bvSize = e.arg(1).get_sort().bv_size();

                    if (isPositive)
                    {
                        return !(e.arg(1) == concat(context->bv_val(1, 1), context->bv_val(0, bvSize - 1)));
                    }
                    else
                    {
                        return context->bool_val(false);
                    }
                }
                else
                {
                    return context->bool_val(false);
                }
            }
            else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1)))
            {
                auto boundType = getBoundType(e.arg(1), boundVars);
                if (boundType == EXISTENTIAL)
                {
                    auto bvSize = e.arg(1).get_sort().bv_size();

                    if (isPositive)
                    {
                        return !(e.arg(0) == concat(context->bv_val(0, 1), context->bv_val(-1, bvSize - 1)));
                    }
                    else
                    {
                        return context->bool_val(false);
                    }
                }
                else
                {
                    return context->bool_val(false);
                }
            }
        }
        else if (decl_kind == Z3_OP_ULEQ)
        {
            if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0)))
            {
                auto boundType = getBoundType(e.arg(0), boundVars);
				auto bvSize = e.arg(1).get_sort().bv_size();                    
				
                if (boundType == EXISTENTIAL)
                {
                    if (isPositive)
                    {
						return context->bool_val(true);
                    }
                    else
                    {
						return !(e.arg(1) == context->bv_val(-1, bvSize));
                    }
                }
                else
                {
					return e.arg(1) == context->bv_val(-1, bvSize);
                }
            }
            else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1)))
            {				
                auto boundType = getBoundType(e.arg(1), boundVars);
				auto bvSize = e.arg(1).get_sort().bv_size();
				
                if (boundType == EXISTENTIAL)
                {
                    if (isPositive)
                    {
						return context->bool_val(true);
                    }
                    else
                    {
						return !(e.arg(0) == context->bv_val(0, bvSize));
                    }
                }
                else
                {
					return e.arg(0) == context->bv_val(0, bvSize);
                }
            }
        }
        else if (decl_kind == Z3_OP_ULT)
        {
            if (isUnconstrained(e.arg(0), boundVars) && isBefore(e.arg(1), e.arg(0)))
            {
                auto boundType = getBoundType(e.arg(0), boundVars);
                if (boundType == EXISTENTIAL)
                {
                    auto bvSize = e.arg(1).get_sort().bv_size();                    

                    if (isPositive)
                    {
                        return !(e.arg(1) == context->bv_val(0, bvSize));
                    }
                    else
                    {
                        return context->bool_val(false);
                    }
                }
                else
                {
                    return context->bool_val(false);
                }
            }
            else if (isUnconstrained(e.arg(1), boundVars) && isBefore(e.arg(0), e.arg(1)))
            {				
                auto boundType = getBoundType(e.arg(1), boundVars);
                if (boundType == EXISTENTIAL)
                {
                    auto bvSize = e.arg(1).get_sort().bv_size();                    

                    if (isPositive)
                    {
                        return !(e.arg(0) == context->bv_val(-1, bvSize));
                    }
                    else
                    {
                        return context->bool_val(false);
                    }
                }
                else
                {
                    return context->bool_val(false);
                }
            }
        }
        else if (decl_kind == Z3_OP_ITE)
		{
			auto result = ite(e.arg(0), simplifyOnce(e.arg(1), boundVars, isPositive), simplifyOnce(e.arg(2), boundVars, isPositive));
      if (isPositive)
      {
			  trueSimplificationCache.insert({(Z3_ast)e, {result, boundVars}});
      }
      else
      {
			  falseSimplificationCache.insert({(Z3_ast)e, {result, boundVars}});
      }
			return result;	  
		}
		
        /*
		for (int i = 0; i < num; i++)
		{
			if (isUnconstrained(e.arg(i), boundVars))
			{
				std::ofstream outfile;
				outfile.open("unconstrained.txt", std::ios_base::app);
				outfile << "unconstrained " << f.name() << " (" << i << ")" << std::endl;
			}
		}
    */

        expr_vector arguments(*context);
        for (unsigned int i = 0; i < num; i++)
        {
            if (decl_kind == Z3_OP_NOT)
            {
                arguments.push_back(simplifyOnce(e.arg(i), boundVars, !isPositive));
            }
            else
            {
                arguments.push_back(simplifyOnce(e.arg(i), boundVars, isPositive));
            }
        }

        auto result = f(arguments);
        if (isPositive)
        {
	    		  trueSimplificationCache.insert({(Z3_ast)e, {result, boundVars}});
        }
        else
        {
			      falseSimplificationCache.insert({(Z3_ast)e, {result, boundVars}});
        }
        return result;
    }
    else if (e.is_quantifier())
    {
        Z3_ast ast = (Z3_ast)e;

        int numBound = Z3_get_quantifier_num_bound(*context, ast);
        BoundType boundType;

		if (isPositive)
		{
			boundType = Z3_is_quantifier_forall(*context, ast) ? UNIVERSAL : EXISTENTIAL;
		}
		else
		{
			boundType = Z3_is_quantifier_forall(*context, ast) ? EXISTENTIAL : UNIVERSAL;
		}
	 

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

    if (isPositive)
    {
	      trueSimplificationCache.insert({(Z3_ast)e, {e, boundVars}});
    }
    else
    {
		    falseSimplificationCache.insert({(Z3_ast)e, {e, boundVars}});
    }        
    return e;
}

bool UnconstrainedVariableSimplifier::isUnconstrained(expr e, const vector<pair<string, BoundType>> &boundVars)
{
    if (!isVar(e) && e.is_app())
    {
		func_decl f = e.decl();
		unsigned num = e.num_args();
      
		if (f.decl_kind() == Z3_OP_EXTRACT)
		{
			return isUnconstrained(e.arg(0), boundVars);
		}
		else
		{	  
			return false;
		}
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
			stringstream ss;
			ss << e;
				
			return (variableCounts[ss.str()] == 1);
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
    return (subformulaMaxDeBruijnIndices[a] >= subformulaMaxDeBruijnIndices[b]) || (subformulaMaxDeBruijnIndices[a] == -1);
}

BoundType UnconstrainedVariableSimplifier::getBoundType(expr e, const std::vector<std::pair<string, BoundType>> &boundVars)
{
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

		if (f.decl_kind() == Z3_OP_EXTRACT)
		{
			return getBoundType(e.arg(0), boundVars);
		}
      
		if (num == 0 && f.name() != NULL)
		{
			return EXISTENTIAL;
		}
    }

    assert(false);
}

int UnconstrainedVariableSimplifier::getNumberOfLeadingZeroes(const z3::expr &e)
{
	assert(e.is_numeral());
	
	std::stringstream ss;
	ss << e;

	string numeralString = ss.str();

	int bitSize = e.get_sort().bv_size();

	const string prefix = numeralString.substr(0, 2);
	string valueString = numeralString.substr(2);

	assert(prefix == "#x" || prefix == "#b");

	std::size_t found = valueString.find_last_not_of("0");

	if (prefix == "#b")
	{
		if (found == std::string::npos)
		{
			return bitSize;
		}
		else
		{
			return bitSize - found - 1;
		}
	}
	else
	{
		if (found == std::string::npos)
		{
			return bitSize;
		}
		else
		{
			int zeroes = bitSize - (found + 1)*4;

			switch (valueString[found])
			{
			case '2':
			case '6':
			case 'a':
			case 'e':
				return zeroes + 1;
			case '4':				
			case 'c':
				return zeroes + 2;
			case '8':
				return zeroes + 3;
			default:
				return zeroes;
			}
		}
		
	}
}
