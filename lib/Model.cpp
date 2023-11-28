#include "Model.h"

#include <iostream>
#include <sstream>


z3::expr substituteModel(z3::expr e, const Model& model)
{
    auto &context = e.ctx();
    z3::expr_vector consts(context);
    z3::expr_vector vals(context);

    for (auto &[varName, modelValue] : model)
    {
	if (std::holds_alternative<bool>(modelValue))
	{
	    consts.push_back(context.bool_const(varName.c_str()));
	    vals.push_back(context.bool_val(std::get<bool>(modelValue)));
	    continue;
	}

	auto bv = std::get<std::vector<bool>>(modelValue);
	auto bitwidth = bv.size();
	z3::expr c = context.bv_const(varName.c_str(), bitwidth);

	std::stringstream ss;
	for (auto bit : bv)
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
    }

    return e.substitute(consts, vals).simplify();
}

std::variant<bool, BitVector> vectorFromNumeral(z3::expr e)
{
    if (e.is_false()) {
	return false;
    }
    if (e.is_true()) {
	return true;
    }

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

void printModelValue(std::string_view name, bool b) {
    std::cout << "  (define-fun " << name << " () bool\n";
    std::cout << "    " << (b ? "true" : "false") << "\n";
    std::cout << "  )\n";

}

void printModelValue(std::string_view name, const BitVector &bv) {
    std::cout << "  (define-fun " << name << " () (_ BitVec " << bv.size() << ")\n";
    std::cout << "    #b";
    for (const auto& bit : bv)
    {
	std::cout << bit;
    }

    std::cout << "  )\n";
}

void printModel(const Model& model)
{
    std::cout << "(model " << std::endl;
    for (const auto& [var, val] : model)
    {
	std::visit([&](auto&& arg) { printModelValue(var, arg); }, val);
    }
    std::cout << ")" << std::endl;
}
