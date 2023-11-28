#include <sstream>

#include "PureLiteralEliminator.h"

using namespace z3;

void PureLiteralEliminator::getVariablePolarities(const z3::expr &e, bool isNegative)
{
    auto item = processedPolaritiesCache.find({(Z3_ast)e, isNegative});
    if (item != processedPolaritiesCache.end())
    {
	return;
    }

    if (e.is_const() && !e.is_numeral())
    {
	std::string expressionString = e.to_string();

	if (e.get_sort().is_bool())
	{
	    if (expressionString == "true" || expressionString == "false")
	    {
		return;
	    }

	    auto polarityIt = variablePolarities.find(expressionString);
	    if (polarityIt == variablePolarities.end())
	    {
		variablePolarities.insert( {expressionString, isNegative ? NEGATIVE : POSITIVE} );
	    }
	    else
	    {
		auto polarity = polarityIt->second;

		if ((polarity == POSITIVE && isNegative) ||
		    (polarity == NEGATIVE && !isNegative))
		{
		    variablePolarities[expressionString] = BOTH_POLARITIES;
		}
	    }
	}
    }
    else if (e.is_app())
    {
	func_decl f = e.decl();
	unsigned num = e.num_args();

	if (f.decl_kind() == Z3_OP_NOT)
	{
	    getVariablePolarities(e.arg(0), !isNegative);
	}
	else if (f.decl_kind() == Z3_OP_ITE)
	{
	    getVariablePolarities(e.arg(0), isNegative);
	    getVariablePolarities(e.arg(0), !isNegative);
	    getVariablePolarities(e.arg(1), isNegative);
	    getVariablePolarities(e.arg(2), isNegative);
	}
	else if (f.decl_kind() == Z3_OP_IFF || (f.decl_kind() == Z3_OP_EQ && e.arg(0).get_sort().is_bool()))
	{
	    getVariablePolarities(e.arg(0), isNegative);
	    getVariablePolarities(e.arg(0), !isNegative);
	    getVariablePolarities(e.arg(1), isNegative);
	    getVariablePolarities(e.arg(1), !isNegative);
	}
	else
	{
	    for (unsigned i = 0; i < num; i++)
	    {
		getVariablePolarities(e.arg(i), isNegative);
	    }
	}
    }
    else if(e.is_quantifier())
    {
        getVariablePolarities(e.body(), isNegative);
    }

    processedPolaritiesCache.insert({(Z3_ast)e, isNegative});
}

z3::expr PureLiteralEliminator::Apply(z3::expr &e)
{
    processedPolaritiesCache.clear();
    variablePolarities.clear();
    getVariablePolarities(e, false);

    z3::expr_vector polaritySubstitutesSrc(*context);
    z3::expr_vector polaritySubstitutesDst(*context);
    for (const auto [var, polarity] : variablePolarities)
    {
	if (polarity == NEGATIVE || polarity == POSITIVE)
	{
	    const auto literal = context->bool_const(var.c_str());
	    polaritySubstitutesSrc.push_back(literal);

	    const auto newValue = context->bool_val(polarity == NEGATIVE ? false : true);
	    polaritySubstitutesDst.push_back(newValue);
	    appliedSubstitutions.push_back({literal, newValue});
	}
    }

    if (polaritySubstitutesSrc.size() == 0)
    {
	return e;
    }
    else
    {
	return e.substitute(polaritySubstitutesSrc, polaritySubstitutesDst);
    }
}

void PureLiteralEliminator::ReconstructModel(Model &model)
{
    for (auto it = appliedSubstitutions.rbegin(); it != appliedSubstitutions.rend(); it++) {
	const auto &[var, subst] = *it;

	std::stringstream variableString;
	variableString << var;

	model[variableString.str()] = vectorFromNumeral(substituteModel(subst, model));
    }
}
