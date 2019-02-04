#pragma once

#include <z3++.h>
#include <string>
#include <map>
#include <functional>
#include <vector>

#include "Solver.h"

#include "SMTLIBv2BaseVisitor.h"

class SMTLIBInterpreter : public SMTLIBv2BaseVisitor
{
public:
    Result Run(SMTLIBv2Parser::ScriptContext*);

    virtual antlrcpp::Any visitCommand(SMTLIBv2Parser::CommandContext *ctx) override;
    virtual antlrcpp::Any visitSort(SMTLIBv2Parser::SortContext *ctx) override;
    virtual antlrcpp::Any visitTerm(SMTLIBv2Parser::TermContext *ctx) override;
    virtual antlrcpp::Any visitSorted_var(SMTLIBv2Parser::Sorted_varContext *ctx) override;
    virtual antlrcpp::Any visitVar_binding(SMTLIBv2Parser::Var_bindingContext *ctx) override;
    virtual antlrcpp::Any visitBinary(SMTLIBv2Parser::BinaryContext *ctx) override;
    virtual antlrcpp::Any visitHexadecimal(SMTLIBv2Parser::HexadecimalContext *ctx) override;
    virtual antlrcpp::Any visitFunction_def(SMTLIBv2Parser::Function_defContext *ctx) override;

    std::map<std::string, std::vector<bool>> GetModel() const { return model; }

    void SetConfig(Config config)
    {
        this->config = config;
    }
private:
    z3::context ctx;
    std::map<std::string, z3::expr> constants;
    std::vector<std::pair<std::string, z3::expr>> variables;
    std::vector<std::pair<std::string, z3::expr>> variableBindings;
    std::map<std::string, std::pair<z3::expr_vector, z3::expr>> funDefinitions;

    void RunCommand(SMTLIBv2Parser::CommandContext*);

    void addConstant(const std::string&, const z3::sort&);
    z3::expr addVar(const std::string&, const z3::sort&);
    void addVarBinding(const std::string&, const z3::expr&);
    z3::expr getConstant(const std::string&) const;
    void addFunctionDefinition(const std::string&, const z3::expr_vector&, const z3::expr&);
    bool isDefinedFunction(const std::string&);
    z3::expr applyDefinedFunction(const std::string&, const z3::expr_vector&);

    Result result = NORESULT;

    Config config;
    std::vector<z3::expr_vector> asserts;

    bool exited = false;
    bool printSuccess = false;

    std::map<std::string, std::vector<bool>> model;
};
