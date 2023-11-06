#include <iostream>

#include <algorithm>
#include <numeric>

#include "SMTLIBInterpreter.h"
#include "Logger.h"
#include "Model.h"

const char* hex_char_to_bin(char c)
{
    switch(toupper(c))
    {
        case '0': return "0000";
        case '1': return "0001";
        case '2': return "0010";
        case '3': return "0011";
        case '4': return "0100";
        case '5': return "0101";
        case '6': return "0110";
        case '7': return "0111";
        case '8': return "1000";
        case '9': return "1001";
        case 'A': return "1010";
        case 'B': return "1011";
        case 'C': return "1100";
        case 'D': return "1101";
        case 'E': return "1110";
        case 'F': return "1111";
    }
}

std::string hex_str_to_bin_str(const std::string& hex)
{
    std::string bin;
    for(unsigned i = 0; i != hex.length(); ++i)
       bin += hex_char_to_bin(hex[i]);
    return bin;
}


Result SMTLIBInterpreter::Run(SMTLIBv2Parser::ScriptContext* script)
{
    asserts.clear();
    asserts.push_back(z3::expr_vector{ctx});

    visitScript(script);
    return result;
}


void SMTLIBInterpreter::addConstant(const std::string& name, const z3::sort& s)
{
    if (s.is_bool())
    {
        constants.insert({name, ctx.bool_const(name.c_str())});
    }
    else if (s.is_bv())
    {
        constants.insert({name, ctx.bv_const(name.c_str(), s.bv_size())});
    }
}

z3::expr SMTLIBInterpreter::addVar(const std::string& name, const z3::sort& s)
{
    if (s.is_bool())
    {
        auto newVar = ctx.bool_const(name.c_str());
        variables.push_back({name, newVar});
        return newVar;
    }
    else if (s.is_bv())
    {
        auto newVar = ctx.bv_const(name.c_str(), s.bv_size());
        variables.push_back({name, newVar});
        return newVar;
    }
    exit(1);
}

void SMTLIBInterpreter::addVarBinding(const std::string& name, const z3::expr& expr)
{
    variableBindings.push_back({name, expr});
}

void SMTLIBInterpreter::addFunctionDefinition(const std::string& name, const z3::expr_vector& args, const z3::expr& body)
{
    funDefinitions.insert({name, {args, body}});
}

void SMTLIBInterpreter::addSortDefinition(const std::string& name,  const z3::sort& sort)
{
    sortDefinitions.insert({name, sort});
}

z3::expr SMTLIBInterpreter::getConstant(const std::string& name) const
{
    auto varItem = std::find_if(
        variables.rbegin(),
        variables.rend(),
        [name] (const auto& it) { return it.first == name; });

    if (varItem != variables.rend())
    {
        return varItem->second;
    }

    auto item = constants.find(name);
    if (item != constants.end())
    {
        return item->second;
    }

    auto bindItem = std::find_if(
        variableBindings.rbegin(),
        variableBindings.rend(),
        [name] (const auto& it) { return it.first == name; });

    if (bindItem != variableBindings.rend())
    {
        return bindItem->second;
    }

    std::cout << "Unknown constant " << name << std::endl;
    exit(1);
}


antlrcpp::Any SMTLIBInterpreter::visitCommand(SMTLIBv2Parser::CommandContext* command)
{
    if (exited) { return antlrcpp::Any{}; }

    if (command->cmd_setLogic())
    {
        std::string logic = command->symbol()[0]->getText();
        if (logic != "BV" && logic != "QF_BV")
        {
            std::cout << "Unsupported logic " << logic;
            exit(1);
        }
    }
    else if (command->cmd_echo())
    {
        std::string str = command->string()->getText();
        std::cout << str.substr(1, str.size()-2) << std::endl;
    }
    else if (command->cmd_exit())
    {
        exited = true;
    }
    else if (command->cmd_getInfo())
    {
        auto info = command->info_flag();
        if (info->PK_Authors())
        {
            std::cout << "(:authors \"Martin Jonas, Jan Strejcek\")" << std::endl;
        }
        else if (info->PK_AssertionStackLevels())
        {
            std::cout << "(:assertion-stack-levels " << (asserts.size() - 1) <<  ")" << std::endl;
        }
        else if (info->PK_ErrorBehaviour())
        {
            std::cout << "(:error-behavior immediate-exit)" << std::endl;
        }
        else if (info->PK_Name())
        {
            std::cout << "(:name \"Q3B\")" << std::endl;
        }
        else if (info->PK_Version())
        {
            std::cout << "1.0" << std::endl;
        }
        else
        {
            std::cout << "unsupported" << std::endl;
        }
    }
    else if (command->cmd_setOption())
    {
        auto option = command->option();
        if (option->PK_DiagnosticOutputChannel())
        {
            //TODO
        }
        else if (option->PK_PrintSuccess())
        {
            printSuccess = option->b_value()->PS_True();
        }
        else if (option->PK_ProduceModels())
        {
            config.produceModels = option->b_value()->PS_True();
        }
        else if (option->PK_RegularOutputChannel())
        {
            //TODO
        }
        else if (option->PK_Verbosity())
        {
            Logger::SetVerbosity(stoul(option->numeral()->getText()));
        }
        else
        {
            std::cout << "unsupported" << std::endl;
        }
    }
    else if (command->cmd_getOption())
    {
        auto option = command->keyword()->predefKeyword();
        if (option->PK_DiagnosticOutputChannel())
        {
            //TODO
        }
        else if (option->PK_PrintSuccess())
        {
            std::cout << ":print-success " << (printSuccess ? "true" : "false") << std::endl;
        }
        else if (option->PK_ProduceModels())
        {
            std::cout << ":produce-models " << (config.produceModels ? "true" : "false") << std::endl;
        }
        else if (option->PK_RegularOutputChannel())
        {
            //TODO
        }
        else if (option->PK_Verbosity())
        {
            std::cout << ":verbosity " << Logger::GetVerbosity() << std::endl;
        }
        else
        {
            std::cout << "unsupported" << std::endl;
        }
    }
    else if (command->cmd_setInfo())
    {
        //TODO: save :status and check its value after solving
    }
    else if (command->cmd_declareFun())
    {
        auto sorts = command->sort();
        if (sorts.size() != 1)
        {
            std::cout << "Uninterpreted functions are not supported" << std::endl;
            exit(1);
        }

        z3::sort s = std::any_cast<z3::sort>(visitSort(sorts[0]));
        std::string name = command->symbol(0)->getText();
        addConstant(name, s);
    }
    else if (command->cmd_declareConst())
    {
        z3::sort s = std::any_cast<z3::sort>(visitSort(command->sort(0)));
        std::string name = command->symbol(0)->getText();
        addConstant(name, s);
    }
    else if (command->cmd_assert())
    {
        assert(!asserts.empty());

        z3::expr formula = std::any_cast<z3::expr>(visitTerm(command->term(0)));
        asserts.back().push_back(formula);
    }
    else if (command->cmd_push())
    {
        unsigned int count = 1;
        if (command->numeral())
        {
            count = stoul(command->numeral()->getText());
        }

        for (unsigned int i = 0; i < count; i++)
        {
            asserts.emplace_back(z3::expr_vector{ctx});
        }
    }
    else if (command->cmd_pop())
    {
        unsigned int count = 1;
        if (command->numeral())
        {
            count = stoul(command->numeral()->getText());
        }

        for (unsigned int i = 0; i < count; i++)
        {
            if (asserts.size() > 1)
            {
                asserts.pop_back();
            }
        }
    }
    else if (command->cmd_reset())
    {
        asserts.clear();
        asserts.emplace_back(z3::expr_vector{ctx});
    }
    else if (command->cmd_resetAssertions())
    {
        asserts.clear();
        asserts.emplace_back(z3::expr_vector{ctx});
    }
    else if (command->cmd_checkSat())
    {
        Solver solver(config);

        auto expr = ctx.bool_val(true);
        for(const auto& assert : asserts)
        {
            expr = expr && z3::mk_and(assert);
        }
        switch(config.approximations)
        {
        case NO_APPROXIMATIONS:
            result = solver.Solve(expr);
            break;
        case ONLY_UNDERAPPROXIMATIONS:
            result = solver.Solve(expr, UNDERAPPROXIMATION, config.precision);
            break;
        case ONLY_OVERAPPROXIMATIONS:
            result = solver.Solve(expr, OVERAPPROXIMATION, config.precision);
            break;
        case ALL_APPROXIMATIONS:
            result = solver.SolveParallel(expr);
            break;
        }

        if (result == SAT && config.produceModels)
        {
            model = solver.GetModel();
        }

        std::cout << (result == SAT ? "sat" :
                      result == UNSAT ? "unsat" :
                      "unknown") << std::endl;
    }
    else if (command->cmd_getModel())
    {
        printModel(model);
    }
    else if (command->cmd_getValue())
    {
        std::cout << "(" << std::endl;
        for (const auto& t : command->term())
        {
            z3::expr termExpr = std::any_cast<z3::expr>(visitTerm(t));
            z3::expr value = substituteModel(termExpr, model).simplify();
            std::cout << "  (" <<  termExpr << " " << value << ")" << std::endl;
        }
        std::cout << ")" << std::endl;
    }
    else if (command->cmd_defineFun())
    {
        visitFunction_def(command->function_def());
    }
    else if (command->cmd_defineSort())
    {
        z3::sort s = std::any_cast<z3::sort>(visitSort(command->sort(0)));
        std::string name = command->symbol(0)->getText();
        addSortDefinition(name, s);
    }

    return antlrcpp::Any{};
}

antlrcpp::Any SMTLIBInterpreter::visitSort(SMTLIBv2Parser::SortContext* sort)
{
    if (auto ident = sort->identifier())
    {
        auto symbol = ident->symbol();

        auto text = symbol->getText();
        if (ident->GRW_Underscore() && text == "BitVec")
        {
            auto index = ident->index(0);
            return ctx.bv_sort(stoi(index->getText()));
        }
        else if (text == "Bool")
        {
            return ctx.bool_sort();
        }
        else if (isDefinedSort(text))
        {
            return sortDefinitions.at(text);
        }
    }

    std::cout << "Unsupported sort " << sort->getText() << std::endl;
    exit(1);
    return antlrcpp::Any{};
}

antlrcpp::Any SMTLIBInterpreter::visitSorted_var(SMTLIBv2Parser::Sorted_varContext* sv)
{
    return addVar(sv->symbol()->getText(), std::any_cast<z3::sort>(visitSort(sv->sort())));
}

antlrcpp::Any SMTLIBInterpreter::visitVar_binding(SMTLIBv2Parser::Var_bindingContext* sv)
{
    addVarBinding(sv->symbol()->getText(), std::any_cast<z3::expr>(visitTerm(sv->term())));
    return antlrcpp::Any{};
}

antlrcpp::Any SMTLIBInterpreter::visitBinary(SMTLIBv2Parser::BinaryContext *b)
{
    std::string bitString = b->getText().substr(2);
    bool bits[bitString.size()];
    int i = bitString.size();
    for (auto& bd : bitString)
    {
        i--;
        bits[i] = bd == '0' ? false : true;
    }
    return ctx.bv_val(bitString.size(), bits);
}

antlrcpp::Any SMTLIBInterpreter::visitHexadecimal(SMTLIBv2Parser::HexadecimalContext *b)
{
    std::string bitString = hex_str_to_bin_str(b->getText().substr(2));
    bool bits[bitString.size()];
    int i = bitString.size();
    for (auto& bd : bitString)
    {
        i--;
        bits[i] = bd == '0' ? false : true;
    }
    return ctx.bv_val(bitString.size(), bits);
}

antlrcpp::Any SMTLIBInterpreter::visitFunction_def(SMTLIBv2Parser::Function_defContext *fd)
{
    std::string name = fd->symbol()->getText();

    z3::expr_vector args(ctx);
    for (auto& sv : fd->sorted_var())
    {
        args.push_back(std::any_cast<z3::expr>(visitSorted_var(sv)));
    }

    addFunctionDefinition(name, args, std::any_cast<z3::expr>(visitTerm(fd->term())));

    variables.clear();
    return antlrcpp::Any{};
}

z3::expr SMTLIBInterpreter::applyDefinedFunction(const std::string& name, const z3::expr_vector& args)
{
    auto [funArgs, body] = funDefinitions.at(name);
    return body.substitute(funArgs, args);
}

bool SMTLIBInterpreter::isDefinedFunction(const std::string& name)
{
    return funDefinitions.find(name) != funDefinitions.end();
}

bool SMTLIBInterpreter::isDefinedSort(const std::string& name)
{
    return sortDefinitions.find(name) != sortDefinitions.end();
}

antlrcpp::Any SMTLIBInterpreter::visitTerm(SMTLIBv2Parser::TermContext* term)
{
    if (auto sc = term->spec_constant())
    {
        if (sc->binary())
        {
            return visitBinary(sc->binary());
        }
        else if (sc->hexadecimal())
        {
            return visitHexadecimal(sc->hexadecimal());
        }
    }

    if (term->GRW_Forall())
    {
        z3::expr_vector bound(ctx);
        for (auto& sv : term->sorted_var())
        {
            bound.push_back(std::any_cast<z3::expr>(visitSorted_var(sv)));
        }
        z3::expr result = z3::forall(bound, std::any_cast<z3::expr>(visitTerm(term->term(0))));

        for (unsigned int i = 0; i < bound.size(); i++)
        {
            variables.pop_back();
        }

        return result;
    }

    if (term->GRW_Exists())
    {
        z3::expr_vector bound(ctx);
        for (auto& sv : term->sorted_var())
        {
            bound.push_back(std::any_cast<z3::expr>(visitSorted_var(sv)));
        }

        z3::expr result = z3::exists(
            bound,
            std::any_cast<z3::expr>(visitTerm(term->term(0))));

        for (unsigned int i = 0; i < bound.size(); i++)
        {
            variables.pop_back();
        }

        return result;
    }

    if (term->GRW_Let())
    {
        for (auto& vb : term->var_binding())
        {
            visitVar_binding(vb);
        }
        z3::expr result = std::any_cast<z3::expr>(visitTerm(term->term(0)));

        for (unsigned int i = 0; i < term->var_binding().size(); i++)
        {
            variableBindings.pop_back();
        }
        return result;
    }

    auto subtermContexts = term->term();
    z3::expr_vector subterms(ctx);

    for( auto& stc : subtermContexts)
    {
        subterms.push_back(std::any_cast<z3::expr>(visitTerm(stc)));
    }

    if (auto ident = term->qual_identifer()->identifier())
    {
        if (ident->GRW_Underscore())
        {
            std::string symbol = ident->symbol()->getText();

            if (symbol.find("bv") == 0)
            {
                std::string value = symbol.substr(2);
                int bw = stoi(ident->index(0)->getText());
                return ctx.bv_val(value.c_str(), bw);
            }
            else if (symbol == "extract")
            {
                return subterms[0].extract(stoi(ident->index(0)->getText()),
                                           stoi(ident->index(1)->getText()));
            }
            else if (symbol == "zero_extend")
            {
                return z3::zext(subterms[0], stoi(ident->index(0)->getText()));
            }
            else if (symbol == "sign_extend")
            {
                return z3::sext(subterms[0], stoi(ident->index(0)->getText()));
            }
            else if (symbol == "repeat")
            {
                auto arg = subterms[0];
                z3::expr_vector concatArgs(ctx);
                for (int i = 0; i < stoi(ident->index(0)->getText()); i++)
                {
                    concatArgs.push_back(arg);
                }
                return z3::concat(concatArgs);
            }
        }

        std::string identName = ident->getText();

        if (identName == "not")
        {
            return !subterms[0];
        }
        else if (identName == "false")
        {
            return ctx.bool_val(false);
        }
        else if (identName == "true")
        {
            return ctx.bool_val(true);
        }
        else if (identName == "and")
        {
            return z3::mk_and(subterms);
        }
        else if (identName == "or")
        {
            return z3::mk_or(subterms);
        }
        else if (identName == "xor")
        {
            return subterms[0] != subterms[1];
        }
        else if (identName == "=>")
        {
            return z3::implies(subterms[0], subterms[1]);
        }
        else if (identName == "ite")
        {
            return z3::ite(subterms[0], subterms[1], subterms[2]);
        }
        else if (identName == "=")
        {
            return subterms[0] == subterms[1];
        }
        else if (identName == "distinct")
        {
            if (subterms[0].get_sort().is_bool()) {
                if (subterms.size() != 2) {
                    std::cout << "Unsupported Boolean distinct of arity > 2" << std::endl;
                    exit(1);
                }
                return !(subterms[0] == subterms[1]);
            } else {
                return z3::distinct(subterms);
            }
        }
        else if (identName == "bvslt")
        {
            return subterms[0] < subterms[1];
        }
        else if (identName == "bvsle")
        {
            return subterms[0] <= subterms[1];
        }
        else if (identName == "bvsge")
        {
            return subterms[0] >= subterms[1];
        }
        else if (identName == "bvsgt")
        {
            return subterms[0] > subterms[1];
        }
        else if (identName == "bvult")
        {
            return z3::ult(subterms[0], subterms[1]);
        }
        else if (identName == "bvule")
        {
            return z3::ule(subterms[0], subterms[1]);
        }
        else if (identName == "bvugt")
        {
            return z3::ugt(subterms[0], subterms[1]);
        }
        else if (identName == "bvuge")
        {
            return z3::uge(subterms[0], subterms[1]);
        }
        else if (identName == "bvneg")
        {
            return -subterms[0];
        }
        else if (identName == "bvmul")
        {
            z3::expr result = subterms[0];
            for (unsigned int i = 1; i < subterms.size(); i++)
            {
                result = result * subterms[i];
            }
            return result;
        }
        else if (identName == "bvadd")
        {
            z3::expr result = subterms[0];
            for (unsigned int i = 1; i < subterms.size(); i++)
            {
                result = result + subterms[i];
            }
            return result;
        }
        else if (identName == "bvsub")
        {
            return subterms[0] - subterms[1];
        }
        else if (identName == "bvsdiv")
        {
            return subterms[0] / subterms[1];
        }
        else if (identName == "bvsrem")
        {
            return z3::srem(subterms[0], subterms[1]);
        }
        else if (identName == "bvudiv")
        {
            return z3::udiv(subterms[0], subterms[1]);
        }
        else if (identName == "bvurem")
        {
            return z3::urem(subterms[0], subterms[1]);
        }
        else if (identName == "concat")
        {
            return z3::concat(subterms);
        }
        else if (identName == "bvor")
        {
            z3::expr result = subterms[0];
            for (unsigned int i = 1; i < subterms.size(); i++)
            {
                result = result | subterms[i];
            }
            return result;
        }
        else if (identName == "bvand")
        {
            z3::expr result = subterms[0];
            for (unsigned int i = 1; i < subterms.size(); i++)
            {
                result = result & subterms[i];
            }
            return result;
        }
        else if (identName == "bvxor")
        {
            z3::expr result = subterms[0];
            for (unsigned int i = 1; i < subterms.size(); i++)
            {
                result = result ^ subterms[i];
            }
            return result;
        }
        else if (identName == "bvxnor")
        {
            z3::expr result = subterms[0];
            for (unsigned int i = 1; i < subterms.size(); i++)
            {
                result = result ^ subterms[i];
            }
            return ~result;
        }
        else if (identName == "bvnot")
        {
            return ~subterms[0];
        }
        else if (identName == "bvshl")
        {
            return z3::shl(subterms[0], subterms[1]);
        }
        else if (identName == "bvashr")
        {
            return z3::ashr(subterms[0], subterms[1]);
        }
        else if (identName == "bvlshr")
        {
            return z3::lshr(subterms[0], subterms[1]);
        }

        if (isDefinedFunction(identName))
        {
            return applyDefinedFunction(identName, subterms);
        }

        if (subterms.empty())
        {
            return getConstant(identName);
        }
    }

    std::cout << "Unsupported term " << term->getText() << std::endl;
    exit(1);
}
