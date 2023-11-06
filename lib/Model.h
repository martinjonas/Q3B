#pragma once

#include <map>
#include <vector>
#include <string>

#include <z3++.h>

using Model = std::map<std::string, std::vector<bool>>;

z3::expr substituteModel(z3::expr e, const Model& model);
std::vector<bool> vectorFromNumeral(z3::expr e);
void printModel(const Model& model);
