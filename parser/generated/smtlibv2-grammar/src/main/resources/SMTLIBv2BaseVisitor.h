
// Generated from smtlibv2-grammar/src/main/resources/SMTLIBv2.g4 by ANTLR 4.7.1

#pragma once


#include "antlr4-runtime.h"
#include "SMTLIBv2Visitor.h"


/**
 * This class provides an empty implementation of SMTLIBv2Visitor, which can be
 * extended to create a visitor which only needs to handle a subset of the available methods.
 */
class  SMTLIBv2BaseVisitor : public SMTLIBv2Visitor {
public:

  virtual antlrcpp::Any visitStart(SMTLIBv2Parser::StartContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitResponse(SMTLIBv2Parser::ResponseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGeneralReservedWord(SMTLIBv2Parser::GeneralReservedWordContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSimpleSymbol(SMTLIBv2Parser::SimpleSymbolContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitQuotedSymbol(SMTLIBv2Parser::QuotedSymbolContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitPredefSymbol(SMTLIBv2Parser::PredefSymbolContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitPredefKeyword(SMTLIBv2Parser::PredefKeywordContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSymbol(SMTLIBv2Parser::SymbolContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitNumeral(SMTLIBv2Parser::NumeralContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitDecimal(SMTLIBv2Parser::DecimalContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitHexadecimal(SMTLIBv2Parser::HexadecimalContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitBinary(SMTLIBv2Parser::BinaryContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitString(SMTLIBv2Parser::StringContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitKeyword(SMTLIBv2Parser::KeywordContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSpec_constant(SMTLIBv2Parser::Spec_constantContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitS_expr(SMTLIBv2Parser::S_exprContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitIndex(SMTLIBv2Parser::IndexContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitIdentifier(SMTLIBv2Parser::IdentifierContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitAttribute_value(SMTLIBv2Parser::Attribute_valueContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitAttribute(SMTLIBv2Parser::AttributeContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSort(SMTLIBv2Parser::SortContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitQual_identifer(SMTLIBv2Parser::Qual_identiferContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitVar_binding(SMTLIBv2Parser::Var_bindingContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSorted_var(SMTLIBv2Parser::Sorted_varContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitPattern(SMTLIBv2Parser::PatternContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitMatch_case(SMTLIBv2Parser::Match_caseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTerm(SMTLIBv2Parser::TermContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSort_symbol_decl(SMTLIBv2Parser::Sort_symbol_declContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitMeta_spec_constant(SMTLIBv2Parser::Meta_spec_constantContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFun_symbol_decl(SMTLIBv2Parser::Fun_symbol_declContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitPar_fun_symbol_decl(SMTLIBv2Parser::Par_fun_symbol_declContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTheory_attribute(SMTLIBv2Parser::Theory_attributeContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitTheory_decl(SMTLIBv2Parser::Theory_declContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitLogic_attribue(SMTLIBv2Parser::Logic_attribueContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitLogic(SMTLIBv2Parser::LogicContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSort_dec(SMTLIBv2Parser::Sort_decContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSelector_dec(SMTLIBv2Parser::Selector_decContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitConstructor_dec(SMTLIBv2Parser::Constructor_decContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitDatatype_dec(SMTLIBv2Parser::Datatype_decContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFunction_dec(SMTLIBv2Parser::Function_decContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitFunction_def(SMTLIBv2Parser::Function_defContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitProp_literal(SMTLIBv2Parser::Prop_literalContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitScript(SMTLIBv2Parser::ScriptContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_assert(SMTLIBv2Parser::Cmd_assertContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_checkSat(SMTLIBv2Parser::Cmd_checkSatContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_checkSatAssuming(SMTLIBv2Parser::Cmd_checkSatAssumingContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_declareConst(SMTLIBv2Parser::Cmd_declareConstContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_declareDatatype(SMTLIBv2Parser::Cmd_declareDatatypeContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_declareDatatypes(SMTLIBv2Parser::Cmd_declareDatatypesContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_declareFun(SMTLIBv2Parser::Cmd_declareFunContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_declareSort(SMTLIBv2Parser::Cmd_declareSortContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_defineFun(SMTLIBv2Parser::Cmd_defineFunContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_defineFunRec(SMTLIBv2Parser::Cmd_defineFunRecContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_defineFunsRec(SMTLIBv2Parser::Cmd_defineFunsRecContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_defineSort(SMTLIBv2Parser::Cmd_defineSortContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_echo(SMTLIBv2Parser::Cmd_echoContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_exit(SMTLIBv2Parser::Cmd_exitContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_getAssertions(SMTLIBv2Parser::Cmd_getAssertionsContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_getAssignment(SMTLIBv2Parser::Cmd_getAssignmentContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_getInfo(SMTLIBv2Parser::Cmd_getInfoContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_getModel(SMTLIBv2Parser::Cmd_getModelContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_getOption(SMTLIBv2Parser::Cmd_getOptionContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_getProof(SMTLIBv2Parser::Cmd_getProofContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_getUnsatAssumptions(SMTLIBv2Parser::Cmd_getUnsatAssumptionsContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_getUnsatCore(SMTLIBv2Parser::Cmd_getUnsatCoreContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_getValue(SMTLIBv2Parser::Cmd_getValueContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_pop(SMTLIBv2Parser::Cmd_popContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_push(SMTLIBv2Parser::Cmd_pushContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_reset(SMTLIBv2Parser::Cmd_resetContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_resetAssertions(SMTLIBv2Parser::Cmd_resetAssertionsContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_setInfo(SMTLIBv2Parser::Cmd_setInfoContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_setLogic(SMTLIBv2Parser::Cmd_setLogicContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCmd_setOption(SMTLIBv2Parser::Cmd_setOptionContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCommand(SMTLIBv2Parser::CommandContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitB_value(SMTLIBv2Parser::B_valueContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitOption(SMTLIBv2Parser::OptionContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitInfo_flag(SMTLIBv2Parser::Info_flagContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitError_behaviour(SMTLIBv2Parser::Error_behaviourContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitReason_unknown(SMTLIBv2Parser::Reason_unknownContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitModel_response(SMTLIBv2Parser::Model_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitInfo_response(SMTLIBv2Parser::Info_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitValuation_pair(SMTLIBv2Parser::Valuation_pairContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitT_valuation_pair(SMTLIBv2Parser::T_valuation_pairContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitCheck_sat_response(SMTLIBv2Parser::Check_sat_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitEcho_response(SMTLIBv2Parser::Echo_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGet_assertions_response(SMTLIBv2Parser::Get_assertions_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGet_assignment_response(SMTLIBv2Parser::Get_assignment_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGet_info_response(SMTLIBv2Parser::Get_info_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGet_model_response(SMTLIBv2Parser::Get_model_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGet_option_response(SMTLIBv2Parser::Get_option_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGet_proof_response(SMTLIBv2Parser::Get_proof_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGet_unsat_assump_response(SMTLIBv2Parser::Get_unsat_assump_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGet_unsat_core_response(SMTLIBv2Parser::Get_unsat_core_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGet_value_response(SMTLIBv2Parser::Get_value_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitSpecific_success_response(SMTLIBv2Parser::Specific_success_responseContext *ctx) override {
    return visitChildren(ctx);
  }

  virtual antlrcpp::Any visitGeneral_response(SMTLIBv2Parser::General_responseContext *ctx) override {
    return visitChildren(ctx);
  }


};

