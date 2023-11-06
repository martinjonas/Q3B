#include "Model.h"

#include <iostream>
#include <sstream>


z3::expr substituteModel(z3::expr e, const Model& model)
{
    auto &context = e.ctx();
    z3::expr_vector consts(context);
    z3::expr_vector vals(context);

    for (auto &varModel : model)
    {
	auto bitwidth = varModel.second.size();
	z3::expr c = context.bv_const(varModel.first.c_str(), bitwidth);

	std::stringstream ss;
	for (auto bit : varModel.second)
	{
	    ss << bit;
	}

	unsigned long long value = 0;
	if (bitwidth <= 8 * sizeof(unsigned long long))
	{
	    value = stoull(ss.str(), 0, 2);
	}

	consts.push_back(c);
        vals.push_back(context.bv_val(static_cast<uint64_t>(value), bitwidth));

	if (bitwidth == 1)
	{
	    consts.push_back(context.bool_const(varModel.first.c_str()));
	    vals.push_back(context.bool_val(varModel.second[0]));
	}
    }


    return e.substitute(consts, vals).simplify();
}

std::vector<bool> vectorFromNumeral(z3::expr e)
{
    std::string binary;
    if (!e.as_binary(binary)) {
	std::cerr << "Error during conversion from value to bit-vector." << std::endl;
	exit(1);
    }

    std::vector<bool> result;
    const auto bitWidth = static_cast<size_t>(e.get_sort().is_bool() ? 1 : e.get_sort().bv_size());
    const auto binarySize = binary.size();

    for (size_t i = 0; i < bitWidth - binarySize; ++i)
    {
	result.push_back(false);
    }

    for (const char bit : binary)
    {
	assert(bit == '0' || bit == '1');
	result.push_back(bit == '1');
    }

    return result;
}


void printModel(const Model& model)
{
    std::cout << "(model " << std::endl;
    for (const auto& [var, val] : model)
    {
	std::cout << "  (define-fun " << var << " () (_ BitVec " << val.size() << ")" << std::endl;;
	std::cout << "    #b";
	for (const auto& bit : val)
	{
	    std::cout << bit;
	}

	std::cout << ")" << std::endl;
    }
    std::cout << ")" << std::endl;
}
