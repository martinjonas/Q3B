
// Generated from smtlibv2-grammar/src/main/resources/SMTLIBv2.g4 by ANTLR 4.7.1

#pragma once


#include "antlr4-runtime.h"
#include "SMTLIBv2Parser.h"



/**
 * This class defines an abstract visitor for a parse tree
 * produced by SMTLIBv2Parser.
 */
class  SMTLIBv2Visitor : public antlr4::tree::AbstractParseTreeVisitor {
public:

  /**
   * Visit parse trees produced by SMTLIBv2Parser.
   */
    virtual antlrcpp::Any visitStart(SMTLIBv2Parser::StartContext *context) = 0;

    virtual antlrcpp::Any visitResponse(SMTLIBv2Parser::ResponseContext *context) = 0;

    virtual antlrcpp::Any visitGeneralReservedWord(SMTLIBv2Parser::GeneralReservedWordContext *context) = 0;

    virtual antlrcpp::Any visitSimpleSymbol(SMTLIBv2Parser::SimpleSymbolContext *context) = 0;

    virtual antlrcpp::Any visitQuotedSymbol(SMTLIBv2Parser::QuotedSymbolContext *context) = 0;

    virtual antlrcpp::Any visitPredefSymbol(SMTLIBv2Parser::PredefSymbolContext *context) = 0;

    virtual antlrcpp::Any visitPredefKeyword(SMTLIBv2Parser::PredefKeywordContext *context) = 0;

    virtual antlrcpp::Any visitSymbol(SMTLIBv2Parser::SymbolContext *context) = 0;

    virtual antlrcpp::Any visitNumeral(SMTLIBv2Parser::NumeralContext *context) = 0;

    virtual antlrcpp::Any visitDecimal(SMTLIBv2Parser::DecimalContext *context) = 0;

    virtual antlrcpp::Any visitHexadecimal(SMTLIBv2Parser::HexadecimalContext *context) = 0;

    virtual antlrcpp::Any visitBinary(SMTLIBv2Parser::BinaryContext *context) = 0;

    virtual antlrcpp::Any visitString(SMTLIBv2Parser::StringContext *context) = 0;

    virtual antlrcpp::Any visitKeyword(SMTLIBv2Parser::KeywordContext *context) = 0;

    virtual antlrcpp::Any visitSpec_constant(SMTLIBv2Parser::Spec_constantContext *context) = 0;

    virtual antlrcpp::Any visitS_expr(SMTLIBv2Parser::S_exprContext *context) = 0;

    virtual antlrcpp::Any visitIndex(SMTLIBv2Parser::IndexContext *context) = 0;

    virtual antlrcpp::Any visitIdentifier(SMTLIBv2Parser::IdentifierContext *context) = 0;

    virtual antlrcpp::Any visitAttribute_value(SMTLIBv2Parser::Attribute_valueContext *context) = 0;

    virtual antlrcpp::Any visitAttribute(SMTLIBv2Parser::AttributeContext *context) = 0;

    virtual antlrcpp::Any visitSort(SMTLIBv2Parser::SortContext *context) = 0;

    virtual antlrcpp::Any visitQual_identifer(SMTLIBv2Parser::Qual_identiferContext *context) = 0;

    virtual antlrcpp::Any visitVar_binding(SMTLIBv2Parser::Var_bindingContext *context) = 0;

    virtual antlrcpp::Any visitSorted_var(SMTLIBv2Parser::Sorted_varContext *context) = 0;

    virtual antlrcpp::Any visitPattern(SMTLIBv2Parser::PatternContext *context) = 0;

    virtual antlrcpp::Any visitMatch_case(SMTLIBv2Parser::Match_caseContext *context) = 0;

    virtual antlrcpp::Any visitTerm(SMTLIBv2Parser::TermContext *context) = 0;

    virtual antlrcpp::Any visitSort_symbol_decl(SMTLIBv2Parser::Sort_symbol_declContext *context) = 0;

    virtual antlrcpp::Any visitMeta_spec_constant(SMTLIBv2Parser::Meta_spec_constantContext *context) = 0;

    virtual antlrcpp::Any visitFun_symbol_decl(SMTLIBv2Parser::Fun_symbol_declContext *context) = 0;

    virtual antlrcpp::Any visitPar_fun_symbol_decl(SMTLIBv2Parser::Par_fun_symbol_declContext *context) = 0;

    virtual antlrcpp::Any visitTheory_attribute(SMTLIBv2Parser::Theory_attributeContext *context) = 0;

    virtual antlrcpp::Any visitTheory_decl(SMTLIBv2Parser::Theory_declContext *context) = 0;

    virtual antlrcpp::Any visitLogic_attribue(SMTLIBv2Parser::Logic_attribueContext *context) = 0;

    virtual antlrcpp::Any visitLogic(SMTLIBv2Parser::LogicContext *context) = 0;

    virtual antlrcpp::Any visitSort_dec(SMTLIBv2Parser::Sort_decContext *context) = 0;

    virtual antlrcpp::Any visitSelector_dec(SMTLIBv2Parser::Selector_decContext *context) = 0;

    virtual antlrcpp::Any visitConstructor_dec(SMTLIBv2Parser::Constructor_decContext *context) = 0;

    virtual antlrcpp::Any visitDatatype_dec(SMTLIBv2Parser::Datatype_decContext *context) = 0;

    virtual antlrcpp::Any visitFunction_dec(SMTLIBv2Parser::Function_decContext *context) = 0;

    virtual antlrcpp::Any visitFunction_def(SMTLIBv2Parser::Function_defContext *context) = 0;

    virtual antlrcpp::Any visitProp_literal(SMTLIBv2Parser::Prop_literalContext *context) = 0;

    virtual antlrcpp::Any visitScript(SMTLIBv2Parser::ScriptContext *context) = 0;

    virtual antlrcpp::Any visitCmd_assert(SMTLIBv2Parser::Cmd_assertContext *context) = 0;

    virtual antlrcpp::Any visitCmd_checkSat(SMTLIBv2Parser::Cmd_checkSatContext *context) = 0;

    virtual antlrcpp::Any visitCmd_checkSatAssuming(SMTLIBv2Parser::Cmd_checkSatAssumingContext *context) = 0;

    virtual antlrcpp::Any visitCmd_declareConst(SMTLIBv2Parser::Cmd_declareConstContext *context) = 0;

    virtual antlrcpp::Any visitCmd_declareDatatype(SMTLIBv2Parser::Cmd_declareDatatypeContext *context) = 0;

    virtual antlrcpp::Any visitCmd_declareDatatypes(SMTLIBv2Parser::Cmd_declareDatatypesContext *context) = 0;

    virtual antlrcpp::Any visitCmd_declareFun(SMTLIBv2Parser::Cmd_declareFunContext *context) = 0;

    virtual antlrcpp::Any visitCmd_declareSort(SMTLIBv2Parser::Cmd_declareSortContext *context) = 0;

    virtual antlrcpp::Any visitCmd_defineFun(SMTLIBv2Parser::Cmd_defineFunContext *context) = 0;

    virtual antlrcpp::Any visitCmd_defineFunRec(SMTLIBv2Parser::Cmd_defineFunRecContext *context) = 0;

    virtual antlrcpp::Any visitCmd_defineFunsRec(SMTLIBv2Parser::Cmd_defineFunsRecContext *context) = 0;

    virtual antlrcpp::Any visitCmd_defineSort(SMTLIBv2Parser::Cmd_defineSortContext *context) = 0;

    virtual antlrcpp::Any visitCmd_echo(SMTLIBv2Parser::Cmd_echoContext *context) = 0;

    virtual antlrcpp::Any visitCmd_exit(SMTLIBv2Parser::Cmd_exitContext *context) = 0;

    virtual antlrcpp::Any visitCmd_getAssertions(SMTLIBv2Parser::Cmd_getAssertionsContext *context) = 0;

    virtual antlrcpp::Any visitCmd_getAssignment(SMTLIBv2Parser::Cmd_getAssignmentContext *context) = 0;

    virtual antlrcpp::Any visitCmd_getInfo(SMTLIBv2Parser::Cmd_getInfoContext *context) = 0;

    virtual antlrcpp::Any visitCmd_getModel(SMTLIBv2Parser::Cmd_getModelContext *context) = 0;

    virtual antlrcpp::Any visitCmd_getOption(SMTLIBv2Parser::Cmd_getOptionContext *context) = 0;

    virtual antlrcpp::Any visitCmd_getProof(SMTLIBv2Parser::Cmd_getProofContext *context) = 0;

    virtual antlrcpp::Any visitCmd_getUnsatAssumptions(SMTLIBv2Parser::Cmd_getUnsatAssumptionsContext *context) = 0;

    virtual antlrcpp::Any visitCmd_getUnsatCore(SMTLIBv2Parser::Cmd_getUnsatCoreContext *context) = 0;

    virtual antlrcpp::Any visitCmd_getValue(SMTLIBv2Parser::Cmd_getValueContext *context) = 0;

    virtual antlrcpp::Any visitCmd_pop(SMTLIBv2Parser::Cmd_popContext *context) = 0;

    virtual antlrcpp::Any visitCmd_push(SMTLIBv2Parser::Cmd_pushContext *context) = 0;

    virtual antlrcpp::Any visitCmd_reset(SMTLIBv2Parser::Cmd_resetContext *context) = 0;

    virtual antlrcpp::Any visitCmd_resetAssertions(SMTLIBv2Parser::Cmd_resetAssertionsContext *context) = 0;

    virtual antlrcpp::Any visitCmd_setInfo(SMTLIBv2Parser::Cmd_setInfoContext *context) = 0;

    virtual antlrcpp::Any visitCmd_setLogic(SMTLIBv2Parser::Cmd_setLogicContext *context) = 0;

    virtual antlrcpp::Any visitCmd_setOption(SMTLIBv2Parser::Cmd_setOptionContext *context) = 0;

    virtual antlrcpp::Any visitCommand(SMTLIBv2Parser::CommandContext *context) = 0;

    virtual antlrcpp::Any visitB_value(SMTLIBv2Parser::B_valueContext *context) = 0;

    virtual antlrcpp::Any visitOption(SMTLIBv2Parser::OptionContext *context) = 0;

    virtual antlrcpp::Any visitInfo_flag(SMTLIBv2Parser::Info_flagContext *context) = 0;

    virtual antlrcpp::Any visitError_behaviour(SMTLIBv2Parser::Error_behaviourContext *context) = 0;

    virtual antlrcpp::Any visitReason_unknown(SMTLIBv2Parser::Reason_unknownContext *context) = 0;

    virtual antlrcpp::Any visitModel_response(SMTLIBv2Parser::Model_responseContext *context) = 0;

    virtual antlrcpp::Any visitInfo_response(SMTLIBv2Parser::Info_responseContext *context) = 0;

    virtual antlrcpp::Any visitValuation_pair(SMTLIBv2Parser::Valuation_pairContext *context) = 0;

    virtual antlrcpp::Any visitT_valuation_pair(SMTLIBv2Parser::T_valuation_pairContext *context) = 0;

    virtual antlrcpp::Any visitCheck_sat_response(SMTLIBv2Parser::Check_sat_responseContext *context) = 0;

    virtual antlrcpp::Any visitEcho_response(SMTLIBv2Parser::Echo_responseContext *context) = 0;

    virtual antlrcpp::Any visitGet_assertions_response(SMTLIBv2Parser::Get_assertions_responseContext *context) = 0;

    virtual antlrcpp::Any visitGet_assignment_response(SMTLIBv2Parser::Get_assignment_responseContext *context) = 0;

    virtual antlrcpp::Any visitGet_info_response(SMTLIBv2Parser::Get_info_responseContext *context) = 0;

    virtual antlrcpp::Any visitGet_model_response(SMTLIBv2Parser::Get_model_responseContext *context) = 0;

    virtual antlrcpp::Any visitGet_option_response(SMTLIBv2Parser::Get_option_responseContext *context) = 0;

    virtual antlrcpp::Any visitGet_proof_response(SMTLIBv2Parser::Get_proof_responseContext *context) = 0;

    virtual antlrcpp::Any visitGet_unsat_assump_response(SMTLIBv2Parser::Get_unsat_assump_responseContext *context) = 0;

    virtual antlrcpp::Any visitGet_unsat_core_response(SMTLIBv2Parser::Get_unsat_core_responseContext *context) = 0;

    virtual antlrcpp::Any visitGet_value_response(SMTLIBv2Parser::Get_value_responseContext *context) = 0;

    virtual antlrcpp::Any visitSpecific_success_response(SMTLIBv2Parser::Specific_success_responseContext *context) = 0;

    virtual antlrcpp::Any visitGeneral_response(SMTLIBv2Parser::General_responseContext *context) = 0;


};

