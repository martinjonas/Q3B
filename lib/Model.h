#pragma once

#include <map>
#include <string>
#include <variant>
#include <vector>

#include <z3++.h>

using BitVector = std::vector<bool>;
using Model = std::map<std::string, std::variant<bool, BitVector>>;

z3::expr substituteModel(z3::expr e, const Model &model);
std::variant<bool, BitVector> vectorFromNumeral(z3::expr e);
void printModel(const Model &model);
