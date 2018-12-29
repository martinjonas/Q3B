
// Generated from smtlibv2-grammar/src/main/resources/SMTLIBv2.g4 by ANTLR 4.7.1

#pragma once


#include "antlr4-runtime.h"




class  SMTLIBv2Parser : public antlr4::Parser {
public:
  enum {
    Comment = 1, ParOpen = 2, ParClose = 3, Semicolon = 4, String = 5, QuotedSymbol = 6, 
    PS_Not = 7, PS_Bool = 8, PS_ContinuedExecution = 9, PS_Error = 10, PS_False = 11, 
    PS_ImmediateExit = 12, PS_Incomplete = 13, PS_Logic = 14, PS_Memout = 15, 
    PS_Sat = 16, PS_Success = 17, PS_Theory = 18, PS_True = 19, PS_Unknown = 20, 
    PS_Unsupported = 21, PS_Unsat = 22, CMD_Assert = 23, CMD_CheckSat = 24, 
    CMD_CheckSatAssuming = 25, CMD_DeclareConst = 26, CMD_DeclareDatatype = 27, 
    CMD_DeclareDatatypes = 28, CMD_DeclareFun = 29, CMD_DeclareSort = 30, 
    CMD_DefineFun = 31, CMD_DefineFunRec = 32, CMD_DefineFunsRec = 33, CMD_DefineSort = 34, 
    CMD_Echo = 35, CMD_Exit = 36, CMD_GetAssertions = 37, CMD_GetAssignment = 38, 
    CMD_GetInfo = 39, CMD_GetModel = 40, CMD_GetOption = 41, CMD_GetProof = 42, 
    CMD_GetUnsatAssumptions = 43, CMD_GetUnsatCore = 44, CMD_GetValue = 45, 
    CMD_Pop = 46, CMD_Push = 47, CMD_Reset = 48, CMD_ResetAssertions = 49, 
    CMD_SetInfo = 50, CMD_SetLogic = 51, CMD_SetOption = 52, GRW_Exclamation = 53, 
    GRW_Underscore = 54, GRW_As = 55, GRW_Binary = 56, GRW_Decimal = 57, 
    GRW_Exists = 58, GRW_Hexadecimal = 59, GRW_Forall = 60, GRW_Let = 61, 
    GRW_Match = 62, GRW_Numeral = 63, GRW_Par = 64, GRW_String = 65, Numeral = 66, 
    Binary = 67, HexDecimal = 68, Decimal = 69, Colon = 70, PK_AllStatistics = 71, 
    PK_AssertionStackLevels = 72, PK_Authors = 73, PK_Category = 74, PK_Chainable = 75, 
    PK_Definition = 76, PK_DiagnosticOutputChannel = 77, PK_ErrorBehaviour = 78, 
    PK_Extension = 79, PK_Funs = 80, PK_FunsDescription = 81, PK_GlobalDeclarations = 82, 
    PK_InteractiveMode = 83, PK_Language = 84, PK_LeftAssoc = 85, PK_License = 86, 
    PK_Named = 87, PK_Name = 88, PK_Notes = 89, PK_Pattern = 90, PK_PrintSuccess = 91, 
    PK_ProduceAssertions = 92, PK_ProduceAssignments = 93, PK_ProduceModels = 94, 
    PK_ProduceProofs = 95, PK_ProduceUnsatAssumptions = 96, PK_ProduceUnsatCores = 97, 
    PK_RandomSeed = 98, PK_ReasonUnknown = 99, PK_RegularOutputChannel = 100, 
    PK_ReproducibleResourceLimit = 101, PK_RightAssoc = 102, PK_SmtLibVersion = 103, 
    PK_Sorts = 104, PK_SortsDescription = 105, PK_Source = 106, PK_Status = 107, 
    PK_Theories = 108, PK_Values = 109, PK_Verbosity = 110, PK_Version = 111, 
    UndefinedSymbol = 112, WS = 113
  };

  enum {
    RuleStart = 0, RuleResponse = 1, RuleGeneralReservedWord = 2, RuleSimpleSymbol = 3, 
    RuleQuotedSymbol = 4, RulePredefSymbol = 5, RulePredefKeyword = 6, RuleSymbol = 7, 
    RuleNumeral = 8, RuleDecimal = 9, RuleHexadecimal = 10, RuleBinary = 11, 
    RuleString = 12, RuleKeyword = 13, RuleSpec_constant = 14, RuleS_expr = 15, 
    RuleIndex = 16, RuleIdentifier = 17, RuleAttribute_value = 18, RuleAttribute = 19, 
    RuleSort = 20, RuleQual_identifer = 21, RuleVar_binding = 22, RuleSorted_var = 23, 
    RulePattern = 24, RuleMatch_case = 25, RuleTerm = 26, RuleSort_symbol_decl = 27, 
    RuleMeta_spec_constant = 28, RuleFun_symbol_decl = 29, RulePar_fun_symbol_decl = 30, 
    RuleTheory_attribute = 31, RuleTheory_decl = 32, RuleLogic_attribue = 33, 
    RuleLogic = 34, RuleSort_dec = 35, RuleSelector_dec = 36, RuleConstructor_dec = 37, 
    RuleDatatype_dec = 38, RuleFunction_dec = 39, RuleFunction_def = 40, 
    RuleProp_literal = 41, RuleScript = 42, RuleCmd_assert = 43, RuleCmd_checkSat = 44, 
    RuleCmd_checkSatAssuming = 45, RuleCmd_declareConst = 46, RuleCmd_declareDatatype = 47, 
    RuleCmd_declareDatatypes = 48, RuleCmd_declareFun = 49, RuleCmd_declareSort = 50, 
    RuleCmd_defineFun = 51, RuleCmd_defineFunRec = 52, RuleCmd_defineFunsRec = 53, 
    RuleCmd_defineSort = 54, RuleCmd_echo = 55, RuleCmd_exit = 56, RuleCmd_getAssertions = 57, 
    RuleCmd_getAssignment = 58, RuleCmd_getInfo = 59, RuleCmd_getModel = 60, 
    RuleCmd_getOption = 61, RuleCmd_getProof = 62, RuleCmd_getUnsatAssumptions = 63, 
    RuleCmd_getUnsatCore = 64, RuleCmd_getValue = 65, RuleCmd_pop = 66, 
    RuleCmd_push = 67, RuleCmd_reset = 68, RuleCmd_resetAssertions = 69, 
    RuleCmd_setInfo = 70, RuleCmd_setLogic = 71, RuleCmd_setOption = 72, 
    RuleCommand = 73, RuleB_value = 74, RuleOption = 75, RuleInfo_flag = 76, 
    RuleError_behaviour = 77, RuleReason_unknown = 78, RuleModel_response = 79, 
    RuleInfo_response = 80, RuleValuation_pair = 81, RuleT_valuation_pair = 82, 
    RuleCheck_sat_response = 83, RuleEcho_response = 84, RuleGet_assertions_response = 85, 
    RuleGet_assignment_response = 86, RuleGet_info_response = 87, RuleGet_model_response = 88, 
    RuleGet_option_response = 89, RuleGet_proof_response = 90, RuleGet_unsat_assump_response = 91, 
    RuleGet_unsat_core_response = 92, RuleGet_value_response = 93, RuleSpecific_success_response = 94, 
    RuleGeneral_response = 95
  };

  SMTLIBv2Parser(antlr4::TokenStream *input);
  ~SMTLIBv2Parser();

  virtual std::string getGrammarFileName() const override;
  virtual const antlr4::atn::ATN& getATN() const override { return _atn; };
  virtual const std::vector<std::string>& getTokenNames() const override { return _tokenNames; }; // deprecated: use vocabulary instead.
  virtual const std::vector<std::string>& getRuleNames() const override;
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;


  class StartContext;
  class ResponseContext;
  class GeneralReservedWordContext;
  class SimpleSymbolContext;
  class QuotedSymbolContext;
  class PredefSymbolContext;
  class PredefKeywordContext;
  class SymbolContext;
  class NumeralContext;
  class DecimalContext;
  class HexadecimalContext;
  class BinaryContext;
  class StringContext;
  class KeywordContext;
  class Spec_constantContext;
  class S_exprContext;
  class IndexContext;
  class IdentifierContext;
  class Attribute_valueContext;
  class AttributeContext;
  class SortContext;
  class Qual_identiferContext;
  class Var_bindingContext;
  class Sorted_varContext;
  class PatternContext;
  class Match_caseContext;
  class TermContext;
  class Sort_symbol_declContext;
  class Meta_spec_constantContext;
  class Fun_symbol_declContext;
  class Par_fun_symbol_declContext;
  class Theory_attributeContext;
  class Theory_declContext;
  class Logic_attribueContext;
  class LogicContext;
  class Sort_decContext;
  class Selector_decContext;
  class Constructor_decContext;
  class Datatype_decContext;
  class Function_decContext;
  class Function_defContext;
  class Prop_literalContext;
  class ScriptContext;
  class Cmd_assertContext;
  class Cmd_checkSatContext;
  class Cmd_checkSatAssumingContext;
  class Cmd_declareConstContext;
  class Cmd_declareDatatypeContext;
  class Cmd_declareDatatypesContext;
  class Cmd_declareFunContext;
  class Cmd_declareSortContext;
  class Cmd_defineFunContext;
  class Cmd_defineFunRecContext;
  class Cmd_defineFunsRecContext;
  class Cmd_defineSortContext;
  class Cmd_echoContext;
  class Cmd_exitContext;
  class Cmd_getAssertionsContext;
  class Cmd_getAssignmentContext;
  class Cmd_getInfoContext;
  class Cmd_getModelContext;
  class Cmd_getOptionContext;
  class Cmd_getProofContext;
  class Cmd_getUnsatAssumptionsContext;
  class Cmd_getUnsatCoreContext;
  class Cmd_getValueContext;
  class Cmd_popContext;
  class Cmd_pushContext;
  class Cmd_resetContext;
  class Cmd_resetAssertionsContext;
  class Cmd_setInfoContext;
  class Cmd_setLogicContext;
  class Cmd_setOptionContext;
  class CommandContext;
  class B_valueContext;
  class OptionContext;
  class Info_flagContext;
  class Error_behaviourContext;
  class Reason_unknownContext;
  class Model_responseContext;
  class Info_responseContext;
  class Valuation_pairContext;
  class T_valuation_pairContext;
  class Check_sat_responseContext;
  class Echo_responseContext;
  class Get_assertions_responseContext;
  class Get_assignment_responseContext;
  class Get_info_responseContext;
  class Get_model_responseContext;
  class Get_option_responseContext;
  class Get_proof_responseContext;
  class Get_unsat_assump_responseContext;
  class Get_unsat_core_responseContext;
  class Get_value_responseContext;
  class Specific_success_responseContext;
  class General_responseContext; 

  class  StartContext : public antlr4::ParserRuleContext {
  public:
    StartContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ScriptContext *script();
    antlr4::tree::TerminalNode *EOF();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  StartContext* start();

  class  ResponseContext : public antlr4::ParserRuleContext {
  public:
    ResponseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    General_responseContext *general_response();
    antlr4::tree::TerminalNode *EOF();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ResponseContext* response();

  class  GeneralReservedWordContext : public antlr4::ParserRuleContext {
  public:
    GeneralReservedWordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *GRW_Exclamation();
    antlr4::tree::TerminalNode *GRW_Underscore();
    antlr4::tree::TerminalNode *GRW_As();
    antlr4::tree::TerminalNode *GRW_Binary();
    antlr4::tree::TerminalNode *GRW_Decimal();
    antlr4::tree::TerminalNode *GRW_Exists();
    antlr4::tree::TerminalNode *GRW_Hexadecimal();
    antlr4::tree::TerminalNode *GRW_Forall();
    antlr4::tree::TerminalNode *GRW_Let();
    antlr4::tree::TerminalNode *GRW_Match();
    antlr4::tree::TerminalNode *GRW_Numeral();
    antlr4::tree::TerminalNode *GRW_Par();
    antlr4::tree::TerminalNode *GRW_String();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  GeneralReservedWordContext* generalReservedWord();

  class  SimpleSymbolContext : public antlr4::ParserRuleContext {
  public:
    SimpleSymbolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    PredefSymbolContext *predefSymbol();
    antlr4::tree::TerminalNode *UndefinedSymbol();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  SimpleSymbolContext* simpleSymbol();

  class  QuotedSymbolContext : public antlr4::ParserRuleContext {
  public:
    QuotedSymbolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *QuotedSymbol();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  QuotedSymbolContext* quotedSymbol();

  class  PredefSymbolContext : public antlr4::ParserRuleContext {
  public:
    PredefSymbolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PS_Not();
    antlr4::tree::TerminalNode *PS_Bool();
    antlr4::tree::TerminalNode *PS_ContinuedExecution();
    antlr4::tree::TerminalNode *PS_Error();
    antlr4::tree::TerminalNode *PS_False();
    antlr4::tree::TerminalNode *PS_ImmediateExit();
    antlr4::tree::TerminalNode *PS_Incomplete();
    antlr4::tree::TerminalNode *PS_Logic();
    antlr4::tree::TerminalNode *PS_Memout();
    antlr4::tree::TerminalNode *PS_Sat();
    antlr4::tree::TerminalNode *PS_Success();
    antlr4::tree::TerminalNode *PS_Theory();
    antlr4::tree::TerminalNode *PS_True();
    antlr4::tree::TerminalNode *PS_Unknown();
    antlr4::tree::TerminalNode *PS_Unsupported();
    antlr4::tree::TerminalNode *PS_Unsat();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  PredefSymbolContext* predefSymbol();

  class  PredefKeywordContext : public antlr4::ParserRuleContext {
  public:
    PredefKeywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PK_AllStatistics();
    antlr4::tree::TerminalNode *PK_AssertionStackLevels();
    antlr4::tree::TerminalNode *PK_Authors();
    antlr4::tree::TerminalNode *PK_Category();
    antlr4::tree::TerminalNode *PK_Chainable();
    antlr4::tree::TerminalNode *PK_Definition();
    antlr4::tree::TerminalNode *PK_DiagnosticOutputChannel();
    antlr4::tree::TerminalNode *PK_ErrorBehaviour();
    antlr4::tree::TerminalNode *PK_Extension();
    antlr4::tree::TerminalNode *PK_Funs();
    antlr4::tree::TerminalNode *PK_FunsDescription();
    antlr4::tree::TerminalNode *PK_GlobalDeclarations();
    antlr4::tree::TerminalNode *PK_InteractiveMode();
    antlr4::tree::TerminalNode *PK_Language();
    antlr4::tree::TerminalNode *PK_LeftAssoc();
    antlr4::tree::TerminalNode *PK_License();
    antlr4::tree::TerminalNode *PK_Named();
    antlr4::tree::TerminalNode *PK_Name();
    antlr4::tree::TerminalNode *PK_Notes();
    antlr4::tree::TerminalNode *PK_Pattern();
    antlr4::tree::TerminalNode *PK_PrintSuccess();
    antlr4::tree::TerminalNode *PK_ProduceAssertions();
    antlr4::tree::TerminalNode *PK_ProduceAssignments();
    antlr4::tree::TerminalNode *PK_ProduceModels();
    antlr4::tree::TerminalNode *PK_ProduceProofs();
    antlr4::tree::TerminalNode *PK_ProduceUnsatAssumptions();
    antlr4::tree::TerminalNode *PK_ProduceUnsatCores();
    antlr4::tree::TerminalNode *PK_RandomSeed();
    antlr4::tree::TerminalNode *PK_ReasonUnknown();
    antlr4::tree::TerminalNode *PK_RegularOutputChannel();
    antlr4::tree::TerminalNode *PK_ReproducibleResourceLimit();
    antlr4::tree::TerminalNode *PK_RightAssoc();
    antlr4::tree::TerminalNode *PK_SmtLibVersion();
    antlr4::tree::TerminalNode *PK_Sorts();
    antlr4::tree::TerminalNode *PK_SortsDescription();
    antlr4::tree::TerminalNode *PK_Source();
    antlr4::tree::TerminalNode *PK_Status();
    antlr4::tree::TerminalNode *PK_Theories();
    antlr4::tree::TerminalNode *PK_Values();
    antlr4::tree::TerminalNode *PK_Verbosity();
    antlr4::tree::TerminalNode *PK_Version();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  PredefKeywordContext* predefKeyword();

  class  SymbolContext : public antlr4::ParserRuleContext {
  public:
    SymbolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    SimpleSymbolContext *simpleSymbol();
    QuotedSymbolContext *quotedSymbol();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  SymbolContext* symbol();

  class  NumeralContext : public antlr4::ParserRuleContext {
  public:
    NumeralContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Numeral();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  NumeralContext* numeral();

  class  DecimalContext : public antlr4::ParserRuleContext {
  public:
    DecimalContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Decimal();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  DecimalContext* decimal();

  class  HexadecimalContext : public antlr4::ParserRuleContext {
  public:
    HexadecimalContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *HexDecimal();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  HexadecimalContext* hexadecimal();

  class  BinaryContext : public antlr4::ParserRuleContext {
  public:
    BinaryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Binary();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  BinaryContext* binary();

  class  StringContext : public antlr4::ParserRuleContext {
  public:
    StringContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *String();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  StringContext* string();

  class  KeywordContext : public antlr4::ParserRuleContext {
  public:
    KeywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    PredefKeywordContext *predefKeyword();
    antlr4::tree::TerminalNode *Colon();
    SimpleSymbolContext *simpleSymbol();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  KeywordContext* keyword();

  class  Spec_constantContext : public antlr4::ParserRuleContext {
  public:
    Spec_constantContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    NumeralContext *numeral();
    DecimalContext *decimal();
    HexadecimalContext *hexadecimal();
    BinaryContext *binary();
    StringContext *string();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Spec_constantContext* spec_constant();

  class  S_exprContext : public antlr4::ParserRuleContext {
  public:
    S_exprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Spec_constantContext *spec_constant();
    SymbolContext *symbol();
    KeywordContext *keyword();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<S_exprContext *> s_expr();
    S_exprContext* s_expr(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  S_exprContext* s_expr();

  class  IndexContext : public antlr4::ParserRuleContext {
  public:
    IndexContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    NumeralContext *numeral();
    SymbolContext *symbol();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  IndexContext* index();

  class  IdentifierContext : public antlr4::ParserRuleContext {
  public:
    IdentifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    SymbolContext *symbol();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *GRW_Underscore();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<IndexContext *> index();
    IndexContext* index(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  IdentifierContext* identifier();

  class  Attribute_valueContext : public antlr4::ParserRuleContext {
  public:
    Attribute_valueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Spec_constantContext *spec_constant();
    SymbolContext *symbol();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<S_exprContext *> s_expr();
    S_exprContext* s_expr(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Attribute_valueContext* attribute_value();

  class  AttributeContext : public antlr4::ParserRuleContext {
  public:
    AttributeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    KeywordContext *keyword();
    Attribute_valueContext *attribute_value();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  AttributeContext* attribute();

  class  SortContext : public antlr4::ParserRuleContext {
  public:
    SortContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<SortContext *> sort();
    SortContext* sort(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  SortContext* sort();

  class  Qual_identiferContext : public antlr4::ParserRuleContext {
  public:
    Qual_identiferContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *GRW_As();
    SortContext *sort();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Qual_identiferContext* qual_identifer();

  class  Var_bindingContext : public antlr4::ParserRuleContext {
  public:
    Var_bindingContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    SymbolContext *symbol();
    TermContext *term();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Var_bindingContext* var_binding();

  class  Sorted_varContext : public antlr4::ParserRuleContext {
  public:
    Sorted_varContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    SymbolContext *symbol();
    SortContext *sort();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Sorted_varContext* sorted_var();

  class  PatternContext : public antlr4::ParserRuleContext {
  public:
    PatternContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<SymbolContext *> symbol();
    SymbolContext* symbol(size_t i);
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  PatternContext* pattern();

  class  Match_caseContext : public antlr4::ParserRuleContext {
  public:
    Match_caseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    PatternContext *pattern();
    TermContext *term();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Match_caseContext* match_case();

  class  TermContext : public antlr4::ParserRuleContext {
  public:
    TermContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Spec_constantContext *spec_constant();
    Qual_identiferContext *qual_identifer();
    std::vector<antlr4::tree::TerminalNode *> ParOpen();
    antlr4::tree::TerminalNode* ParOpen(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ParClose();
    antlr4::tree::TerminalNode* ParClose(size_t i);
    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    antlr4::tree::TerminalNode *GRW_Let();
    std::vector<Var_bindingContext *> var_binding();
    Var_bindingContext* var_binding(size_t i);
    antlr4::tree::TerminalNode *GRW_Forall();
    std::vector<Sorted_varContext *> sorted_var();
    Sorted_varContext* sorted_var(size_t i);
    antlr4::tree::TerminalNode *GRW_Exists();
    antlr4::tree::TerminalNode *GRW_Match();
    std::vector<Match_caseContext *> match_case();
    Match_caseContext* match_case(size_t i);
    antlr4::tree::TerminalNode *GRW_Exclamation();
    std::vector<AttributeContext *> attribute();
    AttributeContext* attribute(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  TermContext* term();

  class  Sort_symbol_declContext : public antlr4::ParserRuleContext {
  public:
    Sort_symbol_declContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    IdentifierContext *identifier();
    NumeralContext *numeral();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<AttributeContext *> attribute();
    AttributeContext* attribute(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Sort_symbol_declContext* sort_symbol_decl();

  class  Meta_spec_constantContext : public antlr4::ParserRuleContext {
  public:
    Meta_spec_constantContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *GRW_Numeral();
    antlr4::tree::TerminalNode *GRW_Decimal();
    antlr4::tree::TerminalNode *GRW_String();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Meta_spec_constantContext* meta_spec_constant();

  class  Fun_symbol_declContext : public antlr4::ParserRuleContext {
  public:
    Fun_symbol_declContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    Spec_constantContext *spec_constant();
    std::vector<SortContext *> sort();
    SortContext* sort(size_t i);
    antlr4::tree::TerminalNode *ParClose();
    std::vector<AttributeContext *> attribute();
    AttributeContext* attribute(size_t i);
    Meta_spec_constantContext *meta_spec_constant();
    IdentifierContext *identifier();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Fun_symbol_declContext* fun_symbol_decl();

  class  Par_fun_symbol_declContext : public antlr4::ParserRuleContext {
  public:
    Par_fun_symbol_declContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Fun_symbol_declContext *fun_symbol_decl();
    std::vector<antlr4::tree::TerminalNode *> ParOpen();
    antlr4::tree::TerminalNode* ParOpen(size_t i);
    antlr4::tree::TerminalNode *GRW_Par();
    std::vector<antlr4::tree::TerminalNode *> ParClose();
    antlr4::tree::TerminalNode* ParClose(size_t i);
    IdentifierContext *identifier();
    std::vector<SymbolContext *> symbol();
    SymbolContext* symbol(size_t i);
    std::vector<SortContext *> sort();
    SortContext* sort(size_t i);
    std::vector<AttributeContext *> attribute();
    AttributeContext* attribute(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Par_fun_symbol_declContext* par_fun_symbol_decl();

  class  Theory_attributeContext : public antlr4::ParserRuleContext {
  public:
    Theory_attributeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PK_Sorts();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<Sort_symbol_declContext *> sort_symbol_decl();
    Sort_symbol_declContext* sort_symbol_decl(size_t i);
    antlr4::tree::TerminalNode *PK_Funs();
    std::vector<Par_fun_symbol_declContext *> par_fun_symbol_decl();
    Par_fun_symbol_declContext* par_fun_symbol_decl(size_t i);
    antlr4::tree::TerminalNode *PK_SortsDescription();
    StringContext *string();
    antlr4::tree::TerminalNode *PK_FunsDescription();
    antlr4::tree::TerminalNode *PK_Definition();
    antlr4::tree::TerminalNode *PK_Values();
    antlr4::tree::TerminalNode *PK_Notes();
    AttributeContext *attribute();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Theory_attributeContext* theory_attribute();

  class  Theory_declContext : public antlr4::ParserRuleContext {
  public:
    Theory_declContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *PS_Theory();
    SymbolContext *symbol();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<Theory_attributeContext *> theory_attribute();
    Theory_attributeContext* theory_attribute(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Theory_declContext* theory_decl();

  class  Logic_attribueContext : public antlr4::ParserRuleContext {
  public:
    Logic_attribueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PK_Theories();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<SymbolContext *> symbol();
    SymbolContext* symbol(size_t i);
    antlr4::tree::TerminalNode *PK_Language();
    StringContext *string();
    antlr4::tree::TerminalNode *PK_Extension();
    antlr4::tree::TerminalNode *PK_Values();
    antlr4::tree::TerminalNode *PK_Notes();
    AttributeContext *attribute();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Logic_attribueContext* logic_attribue();

  class  LogicContext : public antlr4::ParserRuleContext {
  public:
    LogicContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *PS_Logic();
    SymbolContext *symbol();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<Logic_attribueContext *> logic_attribue();
    Logic_attribueContext* logic_attribue(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  LogicContext* logic();

  class  Sort_decContext : public antlr4::ParserRuleContext {
  public:
    Sort_decContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    SymbolContext *symbol();
    NumeralContext *numeral();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Sort_decContext* sort_dec();

  class  Selector_decContext : public antlr4::ParserRuleContext {
  public:
    Selector_decContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    SymbolContext *symbol();
    SortContext *sort();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Selector_decContext* selector_dec();

  class  Constructor_decContext : public antlr4::ParserRuleContext {
  public:
    Constructor_decContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    SymbolContext *symbol();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<Selector_decContext *> selector_dec();
    Selector_decContext* selector_dec(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Constructor_decContext* constructor_dec();

  class  Datatype_decContext : public antlr4::ParserRuleContext {
  public:
    Datatype_decContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> ParOpen();
    antlr4::tree::TerminalNode* ParOpen(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ParClose();
    antlr4::tree::TerminalNode* ParClose(size_t i);
    std::vector<Constructor_decContext *> constructor_dec();
    Constructor_decContext* constructor_dec(size_t i);
    antlr4::tree::TerminalNode *GRW_Par();
    std::vector<SymbolContext *> symbol();
    SymbolContext* symbol(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Datatype_decContext* datatype_dec();

  class  Function_decContext : public antlr4::ParserRuleContext {
  public:
    Function_decContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> ParOpen();
    antlr4::tree::TerminalNode* ParOpen(size_t i);
    SymbolContext *symbol();
    std::vector<antlr4::tree::TerminalNode *> ParClose();
    antlr4::tree::TerminalNode* ParClose(size_t i);
    SortContext *sort();
    std::vector<Sorted_varContext *> sorted_var();
    Sorted_varContext* sorted_var(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Function_decContext* function_dec();

  class  Function_defContext : public antlr4::ParserRuleContext {
  public:
    Function_defContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    SymbolContext *symbol();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    SortContext *sort();
    TermContext *term();
    std::vector<Sorted_varContext *> sorted_var();
    Sorted_varContext* sorted_var(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Function_defContext* function_def();

  class  Prop_literalContext : public antlr4::ParserRuleContext {
  public:
    Prop_literalContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    SymbolContext *symbol();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *PS_Not();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Prop_literalContext* prop_literal();

  class  ScriptContext : public antlr4::ParserRuleContext {
  public:
    ScriptContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<CommandContext *> command();
    CommandContext* command(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  ScriptContext* script();

  class  Cmd_assertContext : public antlr4::ParserRuleContext {
  public:
    Cmd_assertContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_Assert();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_assertContext* cmd_assert();

  class  Cmd_checkSatContext : public antlr4::ParserRuleContext {
  public:
    Cmd_checkSatContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_CheckSat();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_checkSatContext* cmd_checkSat();

  class  Cmd_checkSatAssumingContext : public antlr4::ParserRuleContext {
  public:
    Cmd_checkSatAssumingContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_CheckSatAssuming();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_checkSatAssumingContext* cmd_checkSatAssuming();

  class  Cmd_declareConstContext : public antlr4::ParserRuleContext {
  public:
    Cmd_declareConstContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_DeclareConst();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_declareConstContext* cmd_declareConst();

  class  Cmd_declareDatatypeContext : public antlr4::ParserRuleContext {
  public:
    Cmd_declareDatatypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_DeclareDatatype();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_declareDatatypeContext* cmd_declareDatatype();

  class  Cmd_declareDatatypesContext : public antlr4::ParserRuleContext {
  public:
    Cmd_declareDatatypesContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_DeclareDatatypes();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_declareDatatypesContext* cmd_declareDatatypes();

  class  Cmd_declareFunContext : public antlr4::ParserRuleContext {
  public:
    Cmd_declareFunContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_DeclareFun();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_declareFunContext* cmd_declareFun();

  class  Cmd_declareSortContext : public antlr4::ParserRuleContext {
  public:
    Cmd_declareSortContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_DeclareSort();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_declareSortContext* cmd_declareSort();

  class  Cmd_defineFunContext : public antlr4::ParserRuleContext {
  public:
    Cmd_defineFunContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_DefineFun();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_defineFunContext* cmd_defineFun();

  class  Cmd_defineFunRecContext : public antlr4::ParserRuleContext {
  public:
    Cmd_defineFunRecContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_DefineFunRec();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_defineFunRecContext* cmd_defineFunRec();

  class  Cmd_defineFunsRecContext : public antlr4::ParserRuleContext {
  public:
    Cmd_defineFunsRecContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_DefineFunsRec();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_defineFunsRecContext* cmd_defineFunsRec();

  class  Cmd_defineSortContext : public antlr4::ParserRuleContext {
  public:
    Cmd_defineSortContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_DefineSort();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_defineSortContext* cmd_defineSort();

  class  Cmd_echoContext : public antlr4::ParserRuleContext {
  public:
    Cmd_echoContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_Echo();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_echoContext* cmd_echo();

  class  Cmd_exitContext : public antlr4::ParserRuleContext {
  public:
    Cmd_exitContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_Exit();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_exitContext* cmd_exit();

  class  Cmd_getAssertionsContext : public antlr4::ParserRuleContext {
  public:
    Cmd_getAssertionsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_GetAssertions();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_getAssertionsContext* cmd_getAssertions();

  class  Cmd_getAssignmentContext : public antlr4::ParserRuleContext {
  public:
    Cmd_getAssignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_GetAssignment();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_getAssignmentContext* cmd_getAssignment();

  class  Cmd_getInfoContext : public antlr4::ParserRuleContext {
  public:
    Cmd_getInfoContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_GetInfo();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_getInfoContext* cmd_getInfo();

  class  Cmd_getModelContext : public antlr4::ParserRuleContext {
  public:
    Cmd_getModelContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_GetModel();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_getModelContext* cmd_getModel();

  class  Cmd_getOptionContext : public antlr4::ParserRuleContext {
  public:
    Cmd_getOptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_GetOption();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_getOptionContext* cmd_getOption();

  class  Cmd_getProofContext : public antlr4::ParserRuleContext {
  public:
    Cmd_getProofContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_GetProof();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_getProofContext* cmd_getProof();

  class  Cmd_getUnsatAssumptionsContext : public antlr4::ParserRuleContext {
  public:
    Cmd_getUnsatAssumptionsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_GetUnsatAssumptions();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_getUnsatAssumptionsContext* cmd_getUnsatAssumptions();

  class  Cmd_getUnsatCoreContext : public antlr4::ParserRuleContext {
  public:
    Cmd_getUnsatCoreContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_GetUnsatCore();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_getUnsatCoreContext* cmd_getUnsatCore();

  class  Cmd_getValueContext : public antlr4::ParserRuleContext {
  public:
    Cmd_getValueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_GetValue();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_getValueContext* cmd_getValue();

  class  Cmd_popContext : public antlr4::ParserRuleContext {
  public:
    Cmd_popContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_Pop();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_popContext* cmd_pop();

  class  Cmd_pushContext : public antlr4::ParserRuleContext {
  public:
    Cmd_pushContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_Push();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_pushContext* cmd_push();

  class  Cmd_resetContext : public antlr4::ParserRuleContext {
  public:
    Cmd_resetContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_Reset();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_resetContext* cmd_reset();

  class  Cmd_resetAssertionsContext : public antlr4::ParserRuleContext {
  public:
    Cmd_resetAssertionsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_ResetAssertions();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_resetAssertionsContext* cmd_resetAssertions();

  class  Cmd_setInfoContext : public antlr4::ParserRuleContext {
  public:
    Cmd_setInfoContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_SetInfo();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_setInfoContext* cmd_setInfo();

  class  Cmd_setLogicContext : public antlr4::ParserRuleContext {
  public:
    Cmd_setLogicContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_SetLogic();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_setLogicContext* cmd_setLogic();

  class  Cmd_setOptionContext : public antlr4::ParserRuleContext {
  public:
    Cmd_setOptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CMD_SetOption();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Cmd_setOptionContext* cmd_setOption();

  class  CommandContext : public antlr4::ParserRuleContext {
  public:
    CommandContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> ParOpen();
    antlr4::tree::TerminalNode* ParOpen(size_t i);
    Cmd_assertContext *cmd_assert();
    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ParClose();
    antlr4::tree::TerminalNode* ParClose(size_t i);
    Cmd_checkSatContext *cmd_checkSat();
    Cmd_checkSatAssumingContext *cmd_checkSatAssuming();
    Cmd_declareConstContext *cmd_declareConst();
    std::vector<SymbolContext *> symbol();
    SymbolContext* symbol(size_t i);
    std::vector<SortContext *> sort();
    SortContext* sort(size_t i);
    Cmd_declareDatatypeContext *cmd_declareDatatype();
    std::vector<Datatype_decContext *> datatype_dec();
    Datatype_decContext* datatype_dec(size_t i);
    Cmd_declareDatatypesContext *cmd_declareDatatypes();
    std::vector<Sort_decContext *> sort_dec();
    Sort_decContext* sort_dec(size_t i);
    Cmd_declareFunContext *cmd_declareFun();
    Cmd_declareSortContext *cmd_declareSort();
    NumeralContext *numeral();
    Cmd_defineFunContext *cmd_defineFun();
    Function_defContext *function_def();
    Cmd_defineFunRecContext *cmd_defineFunRec();
    Cmd_defineFunsRecContext *cmd_defineFunsRec();
    std::vector<Function_decContext *> function_dec();
    Function_decContext* function_dec(size_t i);
    Cmd_defineSortContext *cmd_defineSort();
    Cmd_echoContext *cmd_echo();
    StringContext *string();
    Cmd_exitContext *cmd_exit();
    Cmd_getAssertionsContext *cmd_getAssertions();
    Cmd_getAssignmentContext *cmd_getAssignment();
    Cmd_getInfoContext *cmd_getInfo();
    Info_flagContext *info_flag();
    Cmd_getModelContext *cmd_getModel();
    Cmd_getOptionContext *cmd_getOption();
    KeywordContext *keyword();
    Cmd_getProofContext *cmd_getProof();
    Cmd_getUnsatAssumptionsContext *cmd_getUnsatAssumptions();
    Cmd_getUnsatCoreContext *cmd_getUnsatCore();
    Cmd_getValueContext *cmd_getValue();
    Cmd_popContext *cmd_pop();
    Cmd_pushContext *cmd_push();
    Cmd_resetContext *cmd_reset();
    Cmd_resetAssertionsContext *cmd_resetAssertions();
    Cmd_setInfoContext *cmd_setInfo();
    AttributeContext *attribute();
    Cmd_setLogicContext *cmd_setLogic();
    Cmd_setOptionContext *cmd_setOption();
    OptionContext *option();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  CommandContext* command();

  class  B_valueContext : public antlr4::ParserRuleContext {
  public:
    B_valueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PS_True();
    antlr4::tree::TerminalNode *PS_False();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  B_valueContext* b_value();

  class  OptionContext : public antlr4::ParserRuleContext {
  public:
    OptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PK_DiagnosticOutputChannel();
    StringContext *string();
    antlr4::tree::TerminalNode *PK_GlobalDeclarations();
    B_valueContext *b_value();
    antlr4::tree::TerminalNode *PK_InteractiveMode();
    antlr4::tree::TerminalNode *PK_PrintSuccess();
    antlr4::tree::TerminalNode *PK_ProduceAssertions();
    antlr4::tree::TerminalNode *PK_ProduceAssignments();
    antlr4::tree::TerminalNode *PK_ProduceModels();
    antlr4::tree::TerminalNode *PK_ProduceProofs();
    antlr4::tree::TerminalNode *PK_ProduceUnsatAssumptions();
    antlr4::tree::TerminalNode *PK_ProduceUnsatCores();
    antlr4::tree::TerminalNode *PK_RandomSeed();
    NumeralContext *numeral();
    antlr4::tree::TerminalNode *PK_RegularOutputChannel();
    antlr4::tree::TerminalNode *PK_ReproducibleResourceLimit();
    antlr4::tree::TerminalNode *PK_Verbosity();
    AttributeContext *attribute();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  OptionContext* option();

  class  Info_flagContext : public antlr4::ParserRuleContext {
  public:
    Info_flagContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PK_AllStatistics();
    antlr4::tree::TerminalNode *PK_AssertionStackLevels();
    antlr4::tree::TerminalNode *PK_Authors();
    antlr4::tree::TerminalNode *PK_ErrorBehaviour();
    antlr4::tree::TerminalNode *PK_Name();
    antlr4::tree::TerminalNode *PK_ReasonUnknown();
    antlr4::tree::TerminalNode *PK_Version();
    KeywordContext *keyword();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Info_flagContext* info_flag();

  class  Error_behaviourContext : public antlr4::ParserRuleContext {
  public:
    Error_behaviourContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PS_ImmediateExit();
    antlr4::tree::TerminalNode *PS_ContinuedExecution();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Error_behaviourContext* error_behaviour();

  class  Reason_unknownContext : public antlr4::ParserRuleContext {
  public:
    Reason_unknownContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PS_Memout();
    antlr4::tree::TerminalNode *PS_Incomplete();
    S_exprContext *s_expr();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Reason_unknownContext* reason_unknown();

  class  Model_responseContext : public antlr4::ParserRuleContext {
  public:
    Model_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> ParOpen();
    antlr4::tree::TerminalNode* ParOpen(size_t i);
    antlr4::tree::TerminalNode *CMD_DefineFun();
    Function_defContext *function_def();
    std::vector<antlr4::tree::TerminalNode *> ParClose();
    antlr4::tree::TerminalNode* ParClose(size_t i);
    antlr4::tree::TerminalNode *CMD_DefineFunRec();
    antlr4::tree::TerminalNode *CMD_DefineFunsRec();
    std::vector<Function_decContext *> function_dec();
    Function_decContext* function_dec(size_t i);
    std::vector<TermContext *> term();
    TermContext* term(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Model_responseContext* model_response();

  class  Info_responseContext : public antlr4::ParserRuleContext {
  public:
    Info_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PK_AssertionStackLevels();
    NumeralContext *numeral();
    antlr4::tree::TerminalNode *PK_Authors();
    StringContext *string();
    antlr4::tree::TerminalNode *PK_ErrorBehaviour();
    Error_behaviourContext *error_behaviour();
    antlr4::tree::TerminalNode *PK_Name();
    antlr4::tree::TerminalNode *PK_ReasonUnknown();
    Reason_unknownContext *reason_unknown();
    antlr4::tree::TerminalNode *PK_Version();
    AttributeContext *attribute();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Info_responseContext* info_response();

  class  Valuation_pairContext : public antlr4::ParserRuleContext {
  public:
    Valuation_pairContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    std::vector<TermContext *> term();
    TermContext* term(size_t i);
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Valuation_pairContext* valuation_pair();

  class  T_valuation_pairContext : public antlr4::ParserRuleContext {
  public:
    T_valuation_pairContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    SymbolContext *symbol();
    B_valueContext *b_value();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  T_valuation_pairContext* t_valuation_pair();

  class  Check_sat_responseContext : public antlr4::ParserRuleContext {
  public:
    Check_sat_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PS_Sat();
    antlr4::tree::TerminalNode *PS_Unsat();
    antlr4::tree::TerminalNode *PS_Unknown();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Check_sat_responseContext* check_sat_response();

  class  Echo_responseContext : public antlr4::ParserRuleContext {
  public:
    Echo_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    StringContext *string();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Echo_responseContext* echo_response();

  class  Get_assertions_responseContext : public antlr4::ParserRuleContext {
  public:
    Get_assertions_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<TermContext *> term();
    TermContext* term(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Get_assertions_responseContext* get_assertions_response();

  class  Get_assignment_responseContext : public antlr4::ParserRuleContext {
  public:
    Get_assignment_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<T_valuation_pairContext *> t_valuation_pair();
    T_valuation_pairContext* t_valuation_pair(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Get_assignment_responseContext* get_assignment_response();

  class  Get_info_responseContext : public antlr4::ParserRuleContext {
  public:
    Get_info_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<Info_responseContext *> info_response();
    Info_responseContext* info_response(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Get_info_responseContext* get_info_response();

  class  Get_model_responseContext : public antlr4::ParserRuleContext {
  public:
    Get_model_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<Model_responseContext *> model_response();
    Model_responseContext* model_response(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Get_model_responseContext* get_model_response();

  class  Get_option_responseContext : public antlr4::ParserRuleContext {
  public:
    Get_option_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Attribute_valueContext *attribute_value();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Get_option_responseContext* get_option_response();

  class  Get_proof_responseContext : public antlr4::ParserRuleContext {
  public:
    Get_proof_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    S_exprContext *s_expr();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Get_proof_responseContext* get_proof_response();

  class  Get_unsat_assump_responseContext : public antlr4::ParserRuleContext {
  public:
    Get_unsat_assump_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<SymbolContext *> symbol();
    SymbolContext* symbol(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Get_unsat_assump_responseContext* get_unsat_assump_response();

  class  Get_unsat_core_responseContext : public antlr4::ParserRuleContext {
  public:
    Get_unsat_core_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<SymbolContext *> symbol();
    SymbolContext* symbol(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Get_unsat_core_responseContext* get_unsat_core_response();

  class  Get_value_responseContext : public antlr4::ParserRuleContext {
  public:
    Get_value_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *ParClose();
    std::vector<Valuation_pairContext *> valuation_pair();
    Valuation_pairContext* valuation_pair(size_t i);

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Get_value_responseContext* get_value_response();

  class  Specific_success_responseContext : public antlr4::ParserRuleContext {
  public:
    Specific_success_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Check_sat_responseContext *check_sat_response();
    Echo_responseContext *echo_response();
    Get_assertions_responseContext *get_assertions_response();
    Get_assignment_responseContext *get_assignment_response();
    Get_info_responseContext *get_info_response();
    Get_model_responseContext *get_model_response();
    Get_option_responseContext *get_option_response();
    Get_proof_responseContext *get_proof_response();
    Get_unsat_assump_responseContext *get_unsat_assump_response();
    Get_unsat_core_responseContext *get_unsat_core_response();
    Get_value_responseContext *get_value_response();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  Specific_success_responseContext* specific_success_response();

  class  General_responseContext : public antlr4::ParserRuleContext {
  public:
    General_responseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PS_Success();
    Specific_success_responseContext *specific_success_response();
    antlr4::tree::TerminalNode *PS_Unsupported();
    antlr4::tree::TerminalNode *ParOpen();
    antlr4::tree::TerminalNode *PS_Error();
    StringContext *string();
    antlr4::tree::TerminalNode *ParClose();

    virtual antlrcpp::Any accept(antlr4::tree::ParseTreeVisitor *visitor) override;
   
  };

  General_responseContext* general_response();


private:
  static std::vector<antlr4::dfa::DFA> _decisionToDFA;
  static antlr4::atn::PredictionContextCache _sharedContextCache;
  static std::vector<std::string> _ruleNames;
  static std::vector<std::string> _tokenNames;

  static std::vector<std::string> _literalNames;
  static std::vector<std::string> _symbolicNames;
  static antlr4::dfa::Vocabulary _vocabulary;
  static antlr4::atn::ATN _atn;
  static std::vector<uint16_t> _serializedATN;


  struct Initializer {
    Initializer();
  };
  static Initializer _init;
};

