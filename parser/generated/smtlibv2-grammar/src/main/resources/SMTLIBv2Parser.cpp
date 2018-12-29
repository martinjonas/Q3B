
// Generated from smtlibv2-grammar/src/main/resources/SMTLIBv2.g4 by ANTLR 4.7.1


#include "SMTLIBv2Visitor.h"

#include "SMTLIBv2Parser.h"


using namespace antlrcpp;
using namespace antlr4;

SMTLIBv2Parser::SMTLIBv2Parser(TokenStream *input) : Parser(input) {
  _interpreter = new atn::ParserATNSimulator(this, _atn, _decisionToDFA, _sharedContextCache);
}

SMTLIBv2Parser::~SMTLIBv2Parser() {
  delete _interpreter;
}

std::string SMTLIBv2Parser::getGrammarFileName() const {
  return "SMTLIBv2.g4";
}

const std::vector<std::string>& SMTLIBv2Parser::getRuleNames() const {
  return _ruleNames;
}

dfa::Vocabulary& SMTLIBv2Parser::getVocabulary() const {
  return _vocabulary;
}


//----------------- StartContext ------------------------------------------------------------------

SMTLIBv2Parser::StartContext::StartContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::ScriptContext* SMTLIBv2Parser::StartContext::script() {
  return getRuleContext<SMTLIBv2Parser::ScriptContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::StartContext::EOF() {
  return getToken(SMTLIBv2Parser::EOF, 0);
}


size_t SMTLIBv2Parser::StartContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleStart;
}

antlrcpp::Any SMTLIBv2Parser::StartContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitStart(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::StartContext* SMTLIBv2Parser::start() {
  StartContext *_localctx = _tracker.createInstance<StartContext>(_ctx, getState());
  enterRule(_localctx, 0, SMTLIBv2Parser::RuleStart);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(192);
    script();
    setState(193);
    match(SMTLIBv2Parser::EOF);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ResponseContext ------------------------------------------------------------------

SMTLIBv2Parser::ResponseContext::ResponseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::General_responseContext* SMTLIBv2Parser::ResponseContext::general_response() {
  return getRuleContext<SMTLIBv2Parser::General_responseContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::ResponseContext::EOF() {
  return getToken(SMTLIBv2Parser::EOF, 0);
}


size_t SMTLIBv2Parser::ResponseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleResponse;
}

antlrcpp::Any SMTLIBv2Parser::ResponseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitResponse(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::ResponseContext* SMTLIBv2Parser::response() {
  ResponseContext *_localctx = _tracker.createInstance<ResponseContext>(_ctx, getState());
  enterRule(_localctx, 2, SMTLIBv2Parser::RuleResponse);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(195);
    general_response();
    setState(196);
    match(SMTLIBv2Parser::EOF);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- GeneralReservedWordContext ------------------------------------------------------------------

SMTLIBv2Parser::GeneralReservedWordContext::GeneralReservedWordContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Exclamation() {
  return getToken(SMTLIBv2Parser::GRW_Exclamation, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Underscore() {
  return getToken(SMTLIBv2Parser::GRW_Underscore, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_As() {
  return getToken(SMTLIBv2Parser::GRW_As, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Binary() {
  return getToken(SMTLIBv2Parser::GRW_Binary, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Decimal() {
  return getToken(SMTLIBv2Parser::GRW_Decimal, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Exists() {
  return getToken(SMTLIBv2Parser::GRW_Exists, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Hexadecimal() {
  return getToken(SMTLIBv2Parser::GRW_Hexadecimal, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Forall() {
  return getToken(SMTLIBv2Parser::GRW_Forall, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Let() {
  return getToken(SMTLIBv2Parser::GRW_Let, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Match() {
  return getToken(SMTLIBv2Parser::GRW_Match, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Numeral() {
  return getToken(SMTLIBv2Parser::GRW_Numeral, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_Par() {
  return getToken(SMTLIBv2Parser::GRW_Par, 0);
}

tree::TerminalNode* SMTLIBv2Parser::GeneralReservedWordContext::GRW_String() {
  return getToken(SMTLIBv2Parser::GRW_String, 0);
}


size_t SMTLIBv2Parser::GeneralReservedWordContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGeneralReservedWord;
}

antlrcpp::Any SMTLIBv2Parser::GeneralReservedWordContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGeneralReservedWord(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::GeneralReservedWordContext* SMTLIBv2Parser::generalReservedWord() {
  GeneralReservedWordContext *_localctx = _tracker.createInstance<GeneralReservedWordContext>(_ctx, getState());
  enterRule(_localctx, 4, SMTLIBv2Parser::RuleGeneralReservedWord);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(198);
    _la = _input->LA(1);
    if (!(((((_la - 53) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 53)) & ((1ULL << (SMTLIBv2Parser::GRW_Exclamation - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Underscore - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_As - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Binary - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Decimal - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Exists - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Hexadecimal - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Forall - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Let - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Match - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Numeral - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_Par - 53))
      | (1ULL << (SMTLIBv2Parser::GRW_String - 53)))) != 0))) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- SimpleSymbolContext ------------------------------------------------------------------

SMTLIBv2Parser::SimpleSymbolContext::SimpleSymbolContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::PredefSymbolContext* SMTLIBv2Parser::SimpleSymbolContext::predefSymbol() {
  return getRuleContext<SMTLIBv2Parser::PredefSymbolContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::SimpleSymbolContext::UndefinedSymbol() {
  return getToken(SMTLIBv2Parser::UndefinedSymbol, 0);
}


size_t SMTLIBv2Parser::SimpleSymbolContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleSimpleSymbol;
}

antlrcpp::Any SMTLIBv2Parser::SimpleSymbolContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitSimpleSymbol(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::SimpleSymbolContext* SMTLIBv2Parser::simpleSymbol() {
  SimpleSymbolContext *_localctx = _tracker.createInstance<SimpleSymbolContext>(_ctx, getState());
  enterRule(_localctx, 6, SMTLIBv2Parser::RuleSimpleSymbol);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(202);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::PS_Not:
      case SMTLIBv2Parser::PS_Bool:
      case SMTLIBv2Parser::PS_ContinuedExecution:
      case SMTLIBv2Parser::PS_Error:
      case SMTLIBv2Parser::PS_False:
      case SMTLIBv2Parser::PS_ImmediateExit:
      case SMTLIBv2Parser::PS_Incomplete:
      case SMTLIBv2Parser::PS_Logic:
      case SMTLIBv2Parser::PS_Memout:
      case SMTLIBv2Parser::PS_Sat:
      case SMTLIBv2Parser::PS_Success:
      case SMTLIBv2Parser::PS_Theory:
      case SMTLIBv2Parser::PS_True:
      case SMTLIBv2Parser::PS_Unknown:
      case SMTLIBv2Parser::PS_Unsupported:
      case SMTLIBv2Parser::PS_Unsat: {
        enterOuterAlt(_localctx, 1);
        setState(200);
        predefSymbol();
        break;
      }

      case SMTLIBv2Parser::UndefinedSymbol: {
        enterOuterAlt(_localctx, 2);
        setState(201);
        match(SMTLIBv2Parser::UndefinedSymbol);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- QuotedSymbolContext ------------------------------------------------------------------

SMTLIBv2Parser::QuotedSymbolContext::QuotedSymbolContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::QuotedSymbolContext::QuotedSymbol() {
  return getToken(SMTLIBv2Parser::QuotedSymbol, 0);
}


size_t SMTLIBv2Parser::QuotedSymbolContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleQuotedSymbol;
}

antlrcpp::Any SMTLIBv2Parser::QuotedSymbolContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitQuotedSymbol(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::QuotedSymbolContext* SMTLIBv2Parser::quotedSymbol() {
  QuotedSymbolContext *_localctx = _tracker.createInstance<QuotedSymbolContext>(_ctx, getState());
  enterRule(_localctx, 8, SMTLIBv2Parser::RuleQuotedSymbol);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(204);
    match(SMTLIBv2Parser::QuotedSymbol);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PredefSymbolContext ------------------------------------------------------------------

SMTLIBv2Parser::PredefSymbolContext::PredefSymbolContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Not() {
  return getToken(SMTLIBv2Parser::PS_Not, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Bool() {
  return getToken(SMTLIBv2Parser::PS_Bool, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_ContinuedExecution() {
  return getToken(SMTLIBv2Parser::PS_ContinuedExecution, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Error() {
  return getToken(SMTLIBv2Parser::PS_Error, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_False() {
  return getToken(SMTLIBv2Parser::PS_False, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_ImmediateExit() {
  return getToken(SMTLIBv2Parser::PS_ImmediateExit, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Incomplete() {
  return getToken(SMTLIBv2Parser::PS_Incomplete, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Logic() {
  return getToken(SMTLIBv2Parser::PS_Logic, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Memout() {
  return getToken(SMTLIBv2Parser::PS_Memout, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Sat() {
  return getToken(SMTLIBv2Parser::PS_Sat, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Success() {
  return getToken(SMTLIBv2Parser::PS_Success, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Theory() {
  return getToken(SMTLIBv2Parser::PS_Theory, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_True() {
  return getToken(SMTLIBv2Parser::PS_True, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Unknown() {
  return getToken(SMTLIBv2Parser::PS_Unknown, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Unsupported() {
  return getToken(SMTLIBv2Parser::PS_Unsupported, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefSymbolContext::PS_Unsat() {
  return getToken(SMTLIBv2Parser::PS_Unsat, 0);
}


size_t SMTLIBv2Parser::PredefSymbolContext::getRuleIndex() const {
  return SMTLIBv2Parser::RulePredefSymbol;
}

antlrcpp::Any SMTLIBv2Parser::PredefSymbolContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitPredefSymbol(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::PredefSymbolContext* SMTLIBv2Parser::predefSymbol() {
  PredefSymbolContext *_localctx = _tracker.createInstance<PredefSymbolContext>(_ctx, getState());
  enterRule(_localctx, 10, SMTLIBv2Parser::RulePredefSymbol);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(206);
    _la = _input->LA(1);
    if (!((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::PS_Not)
      | (1ULL << SMTLIBv2Parser::PS_Bool)
      | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
      | (1ULL << SMTLIBv2Parser::PS_Error)
      | (1ULL << SMTLIBv2Parser::PS_False)
      | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
      | (1ULL << SMTLIBv2Parser::PS_Incomplete)
      | (1ULL << SMTLIBv2Parser::PS_Logic)
      | (1ULL << SMTLIBv2Parser::PS_Memout)
      | (1ULL << SMTLIBv2Parser::PS_Sat)
      | (1ULL << SMTLIBv2Parser::PS_Success)
      | (1ULL << SMTLIBv2Parser::PS_Theory)
      | (1ULL << SMTLIBv2Parser::PS_True)
      | (1ULL << SMTLIBv2Parser::PS_Unknown)
      | (1ULL << SMTLIBv2Parser::PS_Unsupported)
      | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0))) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PredefKeywordContext ------------------------------------------------------------------

SMTLIBv2Parser::PredefKeywordContext::PredefKeywordContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_AllStatistics() {
  return getToken(SMTLIBv2Parser::PK_AllStatistics, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_AssertionStackLevels() {
  return getToken(SMTLIBv2Parser::PK_AssertionStackLevels, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Authors() {
  return getToken(SMTLIBv2Parser::PK_Authors, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Category() {
  return getToken(SMTLIBv2Parser::PK_Category, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Chainable() {
  return getToken(SMTLIBv2Parser::PK_Chainable, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Definition() {
  return getToken(SMTLIBv2Parser::PK_Definition, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_DiagnosticOutputChannel() {
  return getToken(SMTLIBv2Parser::PK_DiagnosticOutputChannel, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_ErrorBehaviour() {
  return getToken(SMTLIBv2Parser::PK_ErrorBehaviour, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Extension() {
  return getToken(SMTLIBv2Parser::PK_Extension, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Funs() {
  return getToken(SMTLIBv2Parser::PK_Funs, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_FunsDescription() {
  return getToken(SMTLIBv2Parser::PK_FunsDescription, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_GlobalDeclarations() {
  return getToken(SMTLIBv2Parser::PK_GlobalDeclarations, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_InteractiveMode() {
  return getToken(SMTLIBv2Parser::PK_InteractiveMode, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Language() {
  return getToken(SMTLIBv2Parser::PK_Language, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_LeftAssoc() {
  return getToken(SMTLIBv2Parser::PK_LeftAssoc, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_License() {
  return getToken(SMTLIBv2Parser::PK_License, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Named() {
  return getToken(SMTLIBv2Parser::PK_Named, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Name() {
  return getToken(SMTLIBv2Parser::PK_Name, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Notes() {
  return getToken(SMTLIBv2Parser::PK_Notes, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Pattern() {
  return getToken(SMTLIBv2Parser::PK_Pattern, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_PrintSuccess() {
  return getToken(SMTLIBv2Parser::PK_PrintSuccess, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_ProduceAssertions() {
  return getToken(SMTLIBv2Parser::PK_ProduceAssertions, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_ProduceAssignments() {
  return getToken(SMTLIBv2Parser::PK_ProduceAssignments, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_ProduceModels() {
  return getToken(SMTLIBv2Parser::PK_ProduceModels, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_ProduceProofs() {
  return getToken(SMTLIBv2Parser::PK_ProduceProofs, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_ProduceUnsatAssumptions() {
  return getToken(SMTLIBv2Parser::PK_ProduceUnsatAssumptions, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_ProduceUnsatCores() {
  return getToken(SMTLIBv2Parser::PK_ProduceUnsatCores, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_RandomSeed() {
  return getToken(SMTLIBv2Parser::PK_RandomSeed, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_ReasonUnknown() {
  return getToken(SMTLIBv2Parser::PK_ReasonUnknown, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_RegularOutputChannel() {
  return getToken(SMTLIBv2Parser::PK_RegularOutputChannel, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_ReproducibleResourceLimit() {
  return getToken(SMTLIBv2Parser::PK_ReproducibleResourceLimit, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_RightAssoc() {
  return getToken(SMTLIBv2Parser::PK_RightAssoc, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_SmtLibVersion() {
  return getToken(SMTLIBv2Parser::PK_SmtLibVersion, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Sorts() {
  return getToken(SMTLIBv2Parser::PK_Sorts, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_SortsDescription() {
  return getToken(SMTLIBv2Parser::PK_SortsDescription, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Source() {
  return getToken(SMTLIBv2Parser::PK_Source, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Status() {
  return getToken(SMTLIBv2Parser::PK_Status, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Theories() {
  return getToken(SMTLIBv2Parser::PK_Theories, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Values() {
  return getToken(SMTLIBv2Parser::PK_Values, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Verbosity() {
  return getToken(SMTLIBv2Parser::PK_Verbosity, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PredefKeywordContext::PK_Version() {
  return getToken(SMTLIBv2Parser::PK_Version, 0);
}


size_t SMTLIBv2Parser::PredefKeywordContext::getRuleIndex() const {
  return SMTLIBv2Parser::RulePredefKeyword;
}

antlrcpp::Any SMTLIBv2Parser::PredefKeywordContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitPredefKeyword(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::PredefKeywordContext* SMTLIBv2Parser::predefKeyword() {
  PredefKeywordContext *_localctx = _tracker.createInstance<PredefKeywordContext>(_ctx, getState());
  enterRule(_localctx, 12, SMTLIBv2Parser::RulePredefKeyword);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(208);
    _la = _input->LA(1);
    if (!(((((_la - 71) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 71)) & ((1ULL << (SMTLIBv2Parser::PK_AllStatistics - 71))
      | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Authors - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Category - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Chainable - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Definition - 71))
      | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 71))
      | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Extension - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Funs - 71))
      | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 71))
      | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 71))
      | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Language - 71))
      | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 71))
      | (1ULL << (SMTLIBv2Parser::PK_License - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Named - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Name - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Notes - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Pattern - 71))
      | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 71))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 71))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 71))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 71))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 71))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 71))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 71))
      | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 71))
      | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 71))
      | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 71))
      | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 71))
      | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 71))
      | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Sorts - 71))
      | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Source - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Status - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Theories - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Values - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 71))
      | (1ULL << (SMTLIBv2Parser::PK_Version - 71)))) != 0))) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- SymbolContext ------------------------------------------------------------------

SMTLIBv2Parser::SymbolContext::SymbolContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::SimpleSymbolContext* SMTLIBv2Parser::SymbolContext::simpleSymbol() {
  return getRuleContext<SMTLIBv2Parser::SimpleSymbolContext>(0);
}

SMTLIBv2Parser::QuotedSymbolContext* SMTLIBv2Parser::SymbolContext::quotedSymbol() {
  return getRuleContext<SMTLIBv2Parser::QuotedSymbolContext>(0);
}


size_t SMTLIBv2Parser::SymbolContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleSymbol;
}

antlrcpp::Any SMTLIBv2Parser::SymbolContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitSymbol(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::symbol() {
  SymbolContext *_localctx = _tracker.createInstance<SymbolContext>(_ctx, getState());
  enterRule(_localctx, 14, SMTLIBv2Parser::RuleSymbol);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(212);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::PS_Not:
      case SMTLIBv2Parser::PS_Bool:
      case SMTLIBv2Parser::PS_ContinuedExecution:
      case SMTLIBv2Parser::PS_Error:
      case SMTLIBv2Parser::PS_False:
      case SMTLIBv2Parser::PS_ImmediateExit:
      case SMTLIBv2Parser::PS_Incomplete:
      case SMTLIBv2Parser::PS_Logic:
      case SMTLIBv2Parser::PS_Memout:
      case SMTLIBv2Parser::PS_Sat:
      case SMTLIBv2Parser::PS_Success:
      case SMTLIBv2Parser::PS_Theory:
      case SMTLIBv2Parser::PS_True:
      case SMTLIBv2Parser::PS_Unknown:
      case SMTLIBv2Parser::PS_Unsupported:
      case SMTLIBv2Parser::PS_Unsat:
      case SMTLIBv2Parser::UndefinedSymbol: {
        enterOuterAlt(_localctx, 1);
        setState(210);
        simpleSymbol();
        break;
      }

      case SMTLIBv2Parser::QuotedSymbol: {
        enterOuterAlt(_localctx, 2);
        setState(211);
        quotedSymbol();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- NumeralContext ------------------------------------------------------------------

SMTLIBv2Parser::NumeralContext::NumeralContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::NumeralContext::Numeral() {
  return getToken(SMTLIBv2Parser::Numeral, 0);
}


size_t SMTLIBv2Parser::NumeralContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleNumeral;
}

antlrcpp::Any SMTLIBv2Parser::NumeralContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitNumeral(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::NumeralContext* SMTLIBv2Parser::numeral() {
  NumeralContext *_localctx = _tracker.createInstance<NumeralContext>(_ctx, getState());
  enterRule(_localctx, 16, SMTLIBv2Parser::RuleNumeral);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(214);
    match(SMTLIBv2Parser::Numeral);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- DecimalContext ------------------------------------------------------------------

SMTLIBv2Parser::DecimalContext::DecimalContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::DecimalContext::Decimal() {
  return getToken(SMTLIBv2Parser::Decimal, 0);
}


size_t SMTLIBv2Parser::DecimalContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleDecimal;
}

antlrcpp::Any SMTLIBv2Parser::DecimalContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitDecimal(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::DecimalContext* SMTLIBv2Parser::decimal() {
  DecimalContext *_localctx = _tracker.createInstance<DecimalContext>(_ctx, getState());
  enterRule(_localctx, 18, SMTLIBv2Parser::RuleDecimal);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(216);
    match(SMTLIBv2Parser::Decimal);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- HexadecimalContext ------------------------------------------------------------------

SMTLIBv2Parser::HexadecimalContext::HexadecimalContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::HexadecimalContext::HexDecimal() {
  return getToken(SMTLIBv2Parser::HexDecimal, 0);
}


size_t SMTLIBv2Parser::HexadecimalContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleHexadecimal;
}

antlrcpp::Any SMTLIBv2Parser::HexadecimalContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitHexadecimal(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::HexadecimalContext* SMTLIBv2Parser::hexadecimal() {
  HexadecimalContext *_localctx = _tracker.createInstance<HexadecimalContext>(_ctx, getState());
  enterRule(_localctx, 20, SMTLIBv2Parser::RuleHexadecimal);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(218);
    match(SMTLIBv2Parser::HexDecimal);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- BinaryContext ------------------------------------------------------------------

SMTLIBv2Parser::BinaryContext::BinaryContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::BinaryContext::Binary() {
  return getToken(SMTLIBv2Parser::Binary, 0);
}


size_t SMTLIBv2Parser::BinaryContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleBinary;
}

antlrcpp::Any SMTLIBv2Parser::BinaryContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitBinary(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::BinaryContext* SMTLIBv2Parser::binary() {
  BinaryContext *_localctx = _tracker.createInstance<BinaryContext>(_ctx, getState());
  enterRule(_localctx, 22, SMTLIBv2Parser::RuleBinary);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(220);
    match(SMTLIBv2Parser::Binary);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- StringContext ------------------------------------------------------------------

SMTLIBv2Parser::StringContext::StringContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::StringContext::String() {
  return getToken(SMTLIBv2Parser::String, 0);
}


size_t SMTLIBv2Parser::StringContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleString;
}

antlrcpp::Any SMTLIBv2Parser::StringContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitString(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::StringContext* SMTLIBv2Parser::string() {
  StringContext *_localctx = _tracker.createInstance<StringContext>(_ctx, getState());
  enterRule(_localctx, 24, SMTLIBv2Parser::RuleString);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(222);
    match(SMTLIBv2Parser::String);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- KeywordContext ------------------------------------------------------------------

SMTLIBv2Parser::KeywordContext::KeywordContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::PredefKeywordContext* SMTLIBv2Parser::KeywordContext::predefKeyword() {
  return getRuleContext<SMTLIBv2Parser::PredefKeywordContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::KeywordContext::Colon() {
  return getToken(SMTLIBv2Parser::Colon, 0);
}

SMTLIBv2Parser::SimpleSymbolContext* SMTLIBv2Parser::KeywordContext::simpleSymbol() {
  return getRuleContext<SMTLIBv2Parser::SimpleSymbolContext>(0);
}


size_t SMTLIBv2Parser::KeywordContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleKeyword;
}

antlrcpp::Any SMTLIBv2Parser::KeywordContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitKeyword(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::KeywordContext* SMTLIBv2Parser::keyword() {
  KeywordContext *_localctx = _tracker.createInstance<KeywordContext>(_ctx, getState());
  enterRule(_localctx, 26, SMTLIBv2Parser::RuleKeyword);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(227);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::PK_AllStatistics:
      case SMTLIBv2Parser::PK_AssertionStackLevels:
      case SMTLIBv2Parser::PK_Authors:
      case SMTLIBv2Parser::PK_Category:
      case SMTLIBv2Parser::PK_Chainable:
      case SMTLIBv2Parser::PK_Definition:
      case SMTLIBv2Parser::PK_DiagnosticOutputChannel:
      case SMTLIBv2Parser::PK_ErrorBehaviour:
      case SMTLIBv2Parser::PK_Extension:
      case SMTLIBv2Parser::PK_Funs:
      case SMTLIBv2Parser::PK_FunsDescription:
      case SMTLIBv2Parser::PK_GlobalDeclarations:
      case SMTLIBv2Parser::PK_InteractiveMode:
      case SMTLIBv2Parser::PK_Language:
      case SMTLIBv2Parser::PK_LeftAssoc:
      case SMTLIBv2Parser::PK_License:
      case SMTLIBv2Parser::PK_Named:
      case SMTLIBv2Parser::PK_Name:
      case SMTLIBv2Parser::PK_Notes:
      case SMTLIBv2Parser::PK_Pattern:
      case SMTLIBv2Parser::PK_PrintSuccess:
      case SMTLIBv2Parser::PK_ProduceAssertions:
      case SMTLIBv2Parser::PK_ProduceAssignments:
      case SMTLIBv2Parser::PK_ProduceModels:
      case SMTLIBv2Parser::PK_ProduceProofs:
      case SMTLIBv2Parser::PK_ProduceUnsatAssumptions:
      case SMTLIBv2Parser::PK_ProduceUnsatCores:
      case SMTLIBv2Parser::PK_RandomSeed:
      case SMTLIBv2Parser::PK_ReasonUnknown:
      case SMTLIBv2Parser::PK_RegularOutputChannel:
      case SMTLIBv2Parser::PK_ReproducibleResourceLimit:
      case SMTLIBv2Parser::PK_RightAssoc:
      case SMTLIBv2Parser::PK_SmtLibVersion:
      case SMTLIBv2Parser::PK_Sorts:
      case SMTLIBv2Parser::PK_SortsDescription:
      case SMTLIBv2Parser::PK_Source:
      case SMTLIBv2Parser::PK_Status:
      case SMTLIBv2Parser::PK_Theories:
      case SMTLIBv2Parser::PK_Values:
      case SMTLIBv2Parser::PK_Verbosity:
      case SMTLIBv2Parser::PK_Version: {
        enterOuterAlt(_localctx, 1);
        setState(224);
        predefKeyword();
        break;
      }

      case SMTLIBv2Parser::Colon: {
        enterOuterAlt(_localctx, 2);
        setState(225);
        match(SMTLIBv2Parser::Colon);
        setState(226);
        simpleSymbol();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Spec_constantContext ------------------------------------------------------------------

SMTLIBv2Parser::Spec_constantContext::Spec_constantContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::NumeralContext* SMTLIBv2Parser::Spec_constantContext::numeral() {
  return getRuleContext<SMTLIBv2Parser::NumeralContext>(0);
}

SMTLIBv2Parser::DecimalContext* SMTLIBv2Parser::Spec_constantContext::decimal() {
  return getRuleContext<SMTLIBv2Parser::DecimalContext>(0);
}

SMTLIBv2Parser::HexadecimalContext* SMTLIBv2Parser::Spec_constantContext::hexadecimal() {
  return getRuleContext<SMTLIBv2Parser::HexadecimalContext>(0);
}

SMTLIBv2Parser::BinaryContext* SMTLIBv2Parser::Spec_constantContext::binary() {
  return getRuleContext<SMTLIBv2Parser::BinaryContext>(0);
}

SMTLIBv2Parser::StringContext* SMTLIBv2Parser::Spec_constantContext::string() {
  return getRuleContext<SMTLIBv2Parser::StringContext>(0);
}


size_t SMTLIBv2Parser::Spec_constantContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleSpec_constant;
}

antlrcpp::Any SMTLIBv2Parser::Spec_constantContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitSpec_constant(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Spec_constantContext* SMTLIBv2Parser::spec_constant() {
  Spec_constantContext *_localctx = _tracker.createInstance<Spec_constantContext>(_ctx, getState());
  enterRule(_localctx, 28, SMTLIBv2Parser::RuleSpec_constant);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(234);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::Numeral: {
        enterOuterAlt(_localctx, 1);
        setState(229);
        numeral();
        break;
      }

      case SMTLIBv2Parser::Decimal: {
        enterOuterAlt(_localctx, 2);
        setState(230);
        decimal();
        break;
      }

      case SMTLIBv2Parser::HexDecimal: {
        enterOuterAlt(_localctx, 3);
        setState(231);
        hexadecimal();
        break;
      }

      case SMTLIBv2Parser::Binary: {
        enterOuterAlt(_localctx, 4);
        setState(232);
        binary();
        break;
      }

      case SMTLIBv2Parser::String: {
        enterOuterAlt(_localctx, 5);
        setState(233);
        string();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- S_exprContext ------------------------------------------------------------------

SMTLIBv2Parser::S_exprContext::S_exprContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::Spec_constantContext* SMTLIBv2Parser::S_exprContext::spec_constant() {
  return getRuleContext<SMTLIBv2Parser::Spec_constantContext>(0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::S_exprContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

SMTLIBv2Parser::KeywordContext* SMTLIBv2Parser::S_exprContext::keyword() {
  return getRuleContext<SMTLIBv2Parser::KeywordContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::S_exprContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::S_exprContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::S_exprContext *> SMTLIBv2Parser::S_exprContext::s_expr() {
  return getRuleContexts<SMTLIBv2Parser::S_exprContext>();
}

SMTLIBv2Parser::S_exprContext* SMTLIBv2Parser::S_exprContext::s_expr(size_t i) {
  return getRuleContext<SMTLIBv2Parser::S_exprContext>(i);
}


size_t SMTLIBv2Parser::S_exprContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleS_expr;
}

antlrcpp::Any SMTLIBv2Parser::S_exprContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitS_expr(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::S_exprContext* SMTLIBv2Parser::s_expr() {
  S_exprContext *_localctx = _tracker.createInstance<S_exprContext>(_ctx, getState());
  enterRule(_localctx, 30, SMTLIBv2Parser::RuleS_expr);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(247);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::String:
      case SMTLIBv2Parser::Numeral:
      case SMTLIBv2Parser::Binary:
      case SMTLIBv2Parser::HexDecimal:
      case SMTLIBv2Parser::Decimal: {
        enterOuterAlt(_localctx, 1);
        setState(236);
        spec_constant();
        break;
      }

      case SMTLIBv2Parser::QuotedSymbol:
      case SMTLIBv2Parser::PS_Not:
      case SMTLIBv2Parser::PS_Bool:
      case SMTLIBv2Parser::PS_ContinuedExecution:
      case SMTLIBv2Parser::PS_Error:
      case SMTLIBv2Parser::PS_False:
      case SMTLIBv2Parser::PS_ImmediateExit:
      case SMTLIBv2Parser::PS_Incomplete:
      case SMTLIBv2Parser::PS_Logic:
      case SMTLIBv2Parser::PS_Memout:
      case SMTLIBv2Parser::PS_Sat:
      case SMTLIBv2Parser::PS_Success:
      case SMTLIBv2Parser::PS_Theory:
      case SMTLIBv2Parser::PS_True:
      case SMTLIBv2Parser::PS_Unknown:
      case SMTLIBv2Parser::PS_Unsupported:
      case SMTLIBv2Parser::PS_Unsat:
      case SMTLIBv2Parser::UndefinedSymbol: {
        enterOuterAlt(_localctx, 2);
        setState(237);
        symbol();
        break;
      }

      case SMTLIBv2Parser::Colon:
      case SMTLIBv2Parser::PK_AllStatistics:
      case SMTLIBv2Parser::PK_AssertionStackLevels:
      case SMTLIBv2Parser::PK_Authors:
      case SMTLIBv2Parser::PK_Category:
      case SMTLIBv2Parser::PK_Chainable:
      case SMTLIBv2Parser::PK_Definition:
      case SMTLIBv2Parser::PK_DiagnosticOutputChannel:
      case SMTLIBv2Parser::PK_ErrorBehaviour:
      case SMTLIBv2Parser::PK_Extension:
      case SMTLIBv2Parser::PK_Funs:
      case SMTLIBv2Parser::PK_FunsDescription:
      case SMTLIBv2Parser::PK_GlobalDeclarations:
      case SMTLIBv2Parser::PK_InteractiveMode:
      case SMTLIBv2Parser::PK_Language:
      case SMTLIBv2Parser::PK_LeftAssoc:
      case SMTLIBv2Parser::PK_License:
      case SMTLIBv2Parser::PK_Named:
      case SMTLIBv2Parser::PK_Name:
      case SMTLIBv2Parser::PK_Notes:
      case SMTLIBv2Parser::PK_Pattern:
      case SMTLIBv2Parser::PK_PrintSuccess:
      case SMTLIBv2Parser::PK_ProduceAssertions:
      case SMTLIBv2Parser::PK_ProduceAssignments:
      case SMTLIBv2Parser::PK_ProduceModels:
      case SMTLIBv2Parser::PK_ProduceProofs:
      case SMTLIBv2Parser::PK_ProduceUnsatAssumptions:
      case SMTLIBv2Parser::PK_ProduceUnsatCores:
      case SMTLIBv2Parser::PK_RandomSeed:
      case SMTLIBv2Parser::PK_ReasonUnknown:
      case SMTLIBv2Parser::PK_RegularOutputChannel:
      case SMTLIBv2Parser::PK_ReproducibleResourceLimit:
      case SMTLIBv2Parser::PK_RightAssoc:
      case SMTLIBv2Parser::PK_SmtLibVersion:
      case SMTLIBv2Parser::PK_Sorts:
      case SMTLIBv2Parser::PK_SortsDescription:
      case SMTLIBv2Parser::PK_Source:
      case SMTLIBv2Parser::PK_Status:
      case SMTLIBv2Parser::PK_Theories:
      case SMTLIBv2Parser::PK_Values:
      case SMTLIBv2Parser::PK_Verbosity:
      case SMTLIBv2Parser::PK_Version: {
        enterOuterAlt(_localctx, 3);
        setState(238);
        keyword();
        break;
      }

      case SMTLIBv2Parser::ParOpen: {
        enterOuterAlt(_localctx, 4);
        setState(239);
        match(SMTLIBv2Parser::ParOpen);
        setState(243);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while ((((_la & ~ 0x3fULL) == 0) &&
          ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
          | (1ULL << SMTLIBv2Parser::String)
          | (1ULL << SMTLIBv2Parser::QuotedSymbol)
          | (1ULL << SMTLIBv2Parser::PS_Not)
          | (1ULL << SMTLIBv2Parser::PS_Bool)
          | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
          | (1ULL << SMTLIBv2Parser::PS_Error)
          | (1ULL << SMTLIBv2Parser::PS_False)
          | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
          | (1ULL << SMTLIBv2Parser::PS_Incomplete)
          | (1ULL << SMTLIBv2Parser::PS_Logic)
          | (1ULL << SMTLIBv2Parser::PS_Memout)
          | (1ULL << SMTLIBv2Parser::PS_Sat)
          | (1ULL << SMTLIBv2Parser::PS_Success)
          | (1ULL << SMTLIBv2Parser::PS_Theory)
          | (1ULL << SMTLIBv2Parser::PS_True)
          | (1ULL << SMTLIBv2Parser::PS_Unknown)
          | (1ULL << SMTLIBv2Parser::PS_Unsupported)
          | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || ((((_la - 66) & ~ 0x3fULL) == 0) &&
          ((1ULL << (_la - 66)) & ((1ULL << (SMTLIBv2Parser::Numeral - 66))
          | (1ULL << (SMTLIBv2Parser::Binary - 66))
          | (1ULL << (SMTLIBv2Parser::HexDecimal - 66))
          | (1ULL << (SMTLIBv2Parser::Decimal - 66))
          | (1ULL << (SMTLIBv2Parser::Colon - 66))
          | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 66))
          | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Authors - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Category - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Chainable - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Definition - 66))
          | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Extension - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Funs - 66))
          | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 66))
          | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 66))
          | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Language - 66))
          | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 66))
          | (1ULL << (SMTLIBv2Parser::PK_License - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Named - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Name - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Notes - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Pattern - 66))
          | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 66))
          | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 66))
          | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 66))
          | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 66))
          | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Sorts - 66))
          | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Source - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Status - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Theories - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Values - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Version - 66))
          | (1ULL << (SMTLIBv2Parser::UndefinedSymbol - 66)))) != 0)) {
          setState(240);
          s_expr();
          setState(245);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(246);
        match(SMTLIBv2Parser::ParClose);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- IndexContext ------------------------------------------------------------------

SMTLIBv2Parser::IndexContext::IndexContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::NumeralContext* SMTLIBv2Parser::IndexContext::numeral() {
  return getRuleContext<SMTLIBv2Parser::NumeralContext>(0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::IndexContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}


size_t SMTLIBv2Parser::IndexContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleIndex;
}

antlrcpp::Any SMTLIBv2Parser::IndexContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitIndex(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::IndexContext* SMTLIBv2Parser::index() {
  IndexContext *_localctx = _tracker.createInstance<IndexContext>(_ctx, getState());
  enterRule(_localctx, 32, SMTLIBv2Parser::RuleIndex);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(251);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::Numeral: {
        enterOuterAlt(_localctx, 1);
        setState(249);
        numeral();
        break;
      }

      case SMTLIBv2Parser::QuotedSymbol:
      case SMTLIBv2Parser::PS_Not:
      case SMTLIBv2Parser::PS_Bool:
      case SMTLIBv2Parser::PS_ContinuedExecution:
      case SMTLIBv2Parser::PS_Error:
      case SMTLIBv2Parser::PS_False:
      case SMTLIBv2Parser::PS_ImmediateExit:
      case SMTLIBv2Parser::PS_Incomplete:
      case SMTLIBv2Parser::PS_Logic:
      case SMTLIBv2Parser::PS_Memout:
      case SMTLIBv2Parser::PS_Sat:
      case SMTLIBv2Parser::PS_Success:
      case SMTLIBv2Parser::PS_Theory:
      case SMTLIBv2Parser::PS_True:
      case SMTLIBv2Parser::PS_Unknown:
      case SMTLIBv2Parser::PS_Unsupported:
      case SMTLIBv2Parser::PS_Unsat:
      case SMTLIBv2Parser::UndefinedSymbol: {
        enterOuterAlt(_localctx, 2);
        setState(250);
        symbol();
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- IdentifierContext ------------------------------------------------------------------

SMTLIBv2Parser::IdentifierContext::IdentifierContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::IdentifierContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::IdentifierContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::IdentifierContext::GRW_Underscore() {
  return getToken(SMTLIBv2Parser::GRW_Underscore, 0);
}

tree::TerminalNode* SMTLIBv2Parser::IdentifierContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::IndexContext *> SMTLIBv2Parser::IdentifierContext::index() {
  return getRuleContexts<SMTLIBv2Parser::IndexContext>();
}

SMTLIBv2Parser::IndexContext* SMTLIBv2Parser::IdentifierContext::index(size_t i) {
  return getRuleContext<SMTLIBv2Parser::IndexContext>(i);
}


size_t SMTLIBv2Parser::IdentifierContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleIdentifier;
}

antlrcpp::Any SMTLIBv2Parser::IdentifierContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitIdentifier(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::IdentifierContext* SMTLIBv2Parser::identifier() {
  IdentifierContext *_localctx = _tracker.createInstance<IdentifierContext>(_ctx, getState());
  enterRule(_localctx, 34, SMTLIBv2Parser::RuleIdentifier);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(264);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::QuotedSymbol:
      case SMTLIBv2Parser::PS_Not:
      case SMTLIBv2Parser::PS_Bool:
      case SMTLIBv2Parser::PS_ContinuedExecution:
      case SMTLIBv2Parser::PS_Error:
      case SMTLIBv2Parser::PS_False:
      case SMTLIBv2Parser::PS_ImmediateExit:
      case SMTLIBv2Parser::PS_Incomplete:
      case SMTLIBv2Parser::PS_Logic:
      case SMTLIBv2Parser::PS_Memout:
      case SMTLIBv2Parser::PS_Sat:
      case SMTLIBv2Parser::PS_Success:
      case SMTLIBv2Parser::PS_Theory:
      case SMTLIBv2Parser::PS_True:
      case SMTLIBv2Parser::PS_Unknown:
      case SMTLIBv2Parser::PS_Unsupported:
      case SMTLIBv2Parser::PS_Unsat:
      case SMTLIBv2Parser::UndefinedSymbol: {
        enterOuterAlt(_localctx, 1);
        setState(253);
        symbol();
        break;
      }

      case SMTLIBv2Parser::ParOpen: {
        enterOuterAlt(_localctx, 2);
        setState(254);
        match(SMTLIBv2Parser::ParOpen);
        setState(255);
        match(SMTLIBv2Parser::GRW_Underscore);
        setState(256);
        symbol();
        setState(258); 
        _errHandler->sync(this);
        _la = _input->LA(1);
        do {
          setState(257);
          index();
          setState(260); 
          _errHandler->sync(this);
          _la = _input->LA(1);
        } while ((((_la & ~ 0x3fULL) == 0) &&
          ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::QuotedSymbol)
          | (1ULL << SMTLIBv2Parser::PS_Not)
          | (1ULL << SMTLIBv2Parser::PS_Bool)
          | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
          | (1ULL << SMTLIBv2Parser::PS_Error)
          | (1ULL << SMTLIBv2Parser::PS_False)
          | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
          | (1ULL << SMTLIBv2Parser::PS_Incomplete)
          | (1ULL << SMTLIBv2Parser::PS_Logic)
          | (1ULL << SMTLIBv2Parser::PS_Memout)
          | (1ULL << SMTLIBv2Parser::PS_Sat)
          | (1ULL << SMTLIBv2Parser::PS_Success)
          | (1ULL << SMTLIBv2Parser::PS_Theory)
          | (1ULL << SMTLIBv2Parser::PS_True)
          | (1ULL << SMTLIBv2Parser::PS_Unknown)
          | (1ULL << SMTLIBv2Parser::PS_Unsupported)
          | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::Numeral

        || _la == SMTLIBv2Parser::UndefinedSymbol);
        setState(262);
        match(SMTLIBv2Parser::ParClose);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Attribute_valueContext ------------------------------------------------------------------

SMTLIBv2Parser::Attribute_valueContext::Attribute_valueContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::Spec_constantContext* SMTLIBv2Parser::Attribute_valueContext::spec_constant() {
  return getRuleContext<SMTLIBv2Parser::Spec_constantContext>(0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Attribute_valueContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Attribute_valueContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Attribute_valueContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::S_exprContext *> SMTLIBv2Parser::Attribute_valueContext::s_expr() {
  return getRuleContexts<SMTLIBv2Parser::S_exprContext>();
}

SMTLIBv2Parser::S_exprContext* SMTLIBv2Parser::Attribute_valueContext::s_expr(size_t i) {
  return getRuleContext<SMTLIBv2Parser::S_exprContext>(i);
}


size_t SMTLIBv2Parser::Attribute_valueContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleAttribute_value;
}

antlrcpp::Any SMTLIBv2Parser::Attribute_valueContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitAttribute_value(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Attribute_valueContext* SMTLIBv2Parser::attribute_value() {
  Attribute_valueContext *_localctx = _tracker.createInstance<Attribute_valueContext>(_ctx, getState());
  enterRule(_localctx, 36, SMTLIBv2Parser::RuleAttribute_value);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(276);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::String:
      case SMTLIBv2Parser::Numeral:
      case SMTLIBv2Parser::Binary:
      case SMTLIBv2Parser::HexDecimal:
      case SMTLIBv2Parser::Decimal: {
        enterOuterAlt(_localctx, 1);
        setState(266);
        spec_constant();
        break;
      }

      case SMTLIBv2Parser::QuotedSymbol:
      case SMTLIBv2Parser::PS_Not:
      case SMTLIBv2Parser::PS_Bool:
      case SMTLIBv2Parser::PS_ContinuedExecution:
      case SMTLIBv2Parser::PS_Error:
      case SMTLIBv2Parser::PS_False:
      case SMTLIBv2Parser::PS_ImmediateExit:
      case SMTLIBv2Parser::PS_Incomplete:
      case SMTLIBv2Parser::PS_Logic:
      case SMTLIBv2Parser::PS_Memout:
      case SMTLIBv2Parser::PS_Sat:
      case SMTLIBv2Parser::PS_Success:
      case SMTLIBv2Parser::PS_Theory:
      case SMTLIBv2Parser::PS_True:
      case SMTLIBv2Parser::PS_Unknown:
      case SMTLIBv2Parser::PS_Unsupported:
      case SMTLIBv2Parser::PS_Unsat:
      case SMTLIBv2Parser::UndefinedSymbol: {
        enterOuterAlt(_localctx, 2);
        setState(267);
        symbol();
        break;
      }

      case SMTLIBv2Parser::ParOpen: {
        enterOuterAlt(_localctx, 3);
        setState(268);
        match(SMTLIBv2Parser::ParOpen);
        setState(272);
        _errHandler->sync(this);
        _la = _input->LA(1);
        while ((((_la & ~ 0x3fULL) == 0) &&
          ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
          | (1ULL << SMTLIBv2Parser::String)
          | (1ULL << SMTLIBv2Parser::QuotedSymbol)
          | (1ULL << SMTLIBv2Parser::PS_Not)
          | (1ULL << SMTLIBv2Parser::PS_Bool)
          | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
          | (1ULL << SMTLIBv2Parser::PS_Error)
          | (1ULL << SMTLIBv2Parser::PS_False)
          | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
          | (1ULL << SMTLIBv2Parser::PS_Incomplete)
          | (1ULL << SMTLIBv2Parser::PS_Logic)
          | (1ULL << SMTLIBv2Parser::PS_Memout)
          | (1ULL << SMTLIBv2Parser::PS_Sat)
          | (1ULL << SMTLIBv2Parser::PS_Success)
          | (1ULL << SMTLIBv2Parser::PS_Theory)
          | (1ULL << SMTLIBv2Parser::PS_True)
          | (1ULL << SMTLIBv2Parser::PS_Unknown)
          | (1ULL << SMTLIBv2Parser::PS_Unsupported)
          | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || ((((_la - 66) & ~ 0x3fULL) == 0) &&
          ((1ULL << (_la - 66)) & ((1ULL << (SMTLIBv2Parser::Numeral - 66))
          | (1ULL << (SMTLIBv2Parser::Binary - 66))
          | (1ULL << (SMTLIBv2Parser::HexDecimal - 66))
          | (1ULL << (SMTLIBv2Parser::Decimal - 66))
          | (1ULL << (SMTLIBv2Parser::Colon - 66))
          | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 66))
          | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Authors - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Category - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Chainable - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Definition - 66))
          | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Extension - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Funs - 66))
          | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 66))
          | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 66))
          | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Language - 66))
          | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 66))
          | (1ULL << (SMTLIBv2Parser::PK_License - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Named - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Name - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Notes - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Pattern - 66))
          | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 66))
          | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 66))
          | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 66))
          | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 66))
          | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 66))
          | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Sorts - 66))
          | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Source - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Status - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Theories - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Values - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 66))
          | (1ULL << (SMTLIBv2Parser::PK_Version - 66))
          | (1ULL << (SMTLIBv2Parser::UndefinedSymbol - 66)))) != 0)) {
          setState(269);
          s_expr();
          setState(274);
          _errHandler->sync(this);
          _la = _input->LA(1);
        }
        setState(275);
        match(SMTLIBv2Parser::ParClose);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- AttributeContext ------------------------------------------------------------------

SMTLIBv2Parser::AttributeContext::AttributeContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::KeywordContext* SMTLIBv2Parser::AttributeContext::keyword() {
  return getRuleContext<SMTLIBv2Parser::KeywordContext>(0);
}

SMTLIBv2Parser::Attribute_valueContext* SMTLIBv2Parser::AttributeContext::attribute_value() {
  return getRuleContext<SMTLIBv2Parser::Attribute_valueContext>(0);
}


size_t SMTLIBv2Parser::AttributeContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleAttribute;
}

antlrcpp::Any SMTLIBv2Parser::AttributeContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitAttribute(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::attribute() {
  AttributeContext *_localctx = _tracker.createInstance<AttributeContext>(_ctx, getState());
  enterRule(_localctx, 38, SMTLIBv2Parser::RuleAttribute);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(282);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 11, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(278);
      keyword();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(279);
      keyword();
      setState(280);
      attribute_value();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- SortContext ------------------------------------------------------------------

SMTLIBv2Parser::SortContext::SortContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::IdentifierContext* SMTLIBv2Parser::SortContext::identifier() {
  return getRuleContext<SMTLIBv2Parser::IdentifierContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::SortContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::SortContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::SortContext *> SMTLIBv2Parser::SortContext::sort() {
  return getRuleContexts<SMTLIBv2Parser::SortContext>();
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::SortContext::sort(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SortContext>(i);
}


size_t SMTLIBv2Parser::SortContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleSort;
}

antlrcpp::Any SMTLIBv2Parser::SortContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitSort(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::sort() {
  SortContext *_localctx = _tracker.createInstance<SortContext>(_ctx, getState());
  enterRule(_localctx, 40, SMTLIBv2Parser::RuleSort);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(294);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 13, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(284);
      identifier();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(285);
      match(SMTLIBv2Parser::ParOpen);
      setState(286);
      identifier();
      setState(288); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(287);
        sort();
        setState(290); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
        | (1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol);
      setState(292);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Qual_identiferContext ------------------------------------------------------------------

SMTLIBv2Parser::Qual_identiferContext::Qual_identiferContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::IdentifierContext* SMTLIBv2Parser::Qual_identiferContext::identifier() {
  return getRuleContext<SMTLIBv2Parser::IdentifierContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Qual_identiferContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Qual_identiferContext::GRW_As() {
  return getToken(SMTLIBv2Parser::GRW_As, 0);
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::Qual_identiferContext::sort() {
  return getRuleContext<SMTLIBv2Parser::SortContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Qual_identiferContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::Qual_identiferContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleQual_identifer;
}

antlrcpp::Any SMTLIBv2Parser::Qual_identiferContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitQual_identifer(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Qual_identiferContext* SMTLIBv2Parser::qual_identifer() {
  Qual_identiferContext *_localctx = _tracker.createInstance<Qual_identiferContext>(_ctx, getState());
  enterRule(_localctx, 42, SMTLIBv2Parser::RuleQual_identifer);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(303);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 14, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(296);
      identifier();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(297);
      match(SMTLIBv2Parser::ParOpen);
      setState(298);
      match(SMTLIBv2Parser::GRW_As);
      setState(299);
      identifier();
      setState(300);
      sort();
      setState(301);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Var_bindingContext ------------------------------------------------------------------

SMTLIBv2Parser::Var_bindingContext::Var_bindingContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Var_bindingContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Var_bindingContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

SMTLIBv2Parser::TermContext* SMTLIBv2Parser::Var_bindingContext::term() {
  return getRuleContext<SMTLIBv2Parser::TermContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Var_bindingContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::Var_bindingContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleVar_binding;
}

antlrcpp::Any SMTLIBv2Parser::Var_bindingContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitVar_binding(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Var_bindingContext* SMTLIBv2Parser::var_binding() {
  Var_bindingContext *_localctx = _tracker.createInstance<Var_bindingContext>(_ctx, getState());
  enterRule(_localctx, 44, SMTLIBv2Parser::RuleVar_binding);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(305);
    match(SMTLIBv2Parser::ParOpen);
    setState(306);
    symbol();
    setState(307);
    term();
    setState(308);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Sorted_varContext ------------------------------------------------------------------

SMTLIBv2Parser::Sorted_varContext::Sorted_varContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Sorted_varContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Sorted_varContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::Sorted_varContext::sort() {
  return getRuleContext<SMTLIBv2Parser::SortContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Sorted_varContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::Sorted_varContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleSorted_var;
}

antlrcpp::Any SMTLIBv2Parser::Sorted_varContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitSorted_var(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Sorted_varContext* SMTLIBv2Parser::sorted_var() {
  Sorted_varContext *_localctx = _tracker.createInstance<Sorted_varContext>(_ctx, getState());
  enterRule(_localctx, 46, SMTLIBv2Parser::RuleSorted_var);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(310);
    match(SMTLIBv2Parser::ParOpen);
    setState(311);
    symbol();
    setState(312);
    sort();
    setState(313);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- PatternContext ------------------------------------------------------------------

SMTLIBv2Parser::PatternContext::PatternContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<SMTLIBv2Parser::SymbolContext *> SMTLIBv2Parser::PatternContext::symbol() {
  return getRuleContexts<SMTLIBv2Parser::SymbolContext>();
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::PatternContext::symbol(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::PatternContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::PatternContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::PatternContext::getRuleIndex() const {
  return SMTLIBv2Parser::RulePattern;
}

antlrcpp::Any SMTLIBv2Parser::PatternContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitPattern(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::PatternContext* SMTLIBv2Parser::pattern() {
  PatternContext *_localctx = _tracker.createInstance<PatternContext>(_ctx, getState());
  enterRule(_localctx, 48, SMTLIBv2Parser::RulePattern);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(325);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::QuotedSymbol:
      case SMTLIBv2Parser::PS_Not:
      case SMTLIBv2Parser::PS_Bool:
      case SMTLIBv2Parser::PS_ContinuedExecution:
      case SMTLIBv2Parser::PS_Error:
      case SMTLIBv2Parser::PS_False:
      case SMTLIBv2Parser::PS_ImmediateExit:
      case SMTLIBv2Parser::PS_Incomplete:
      case SMTLIBv2Parser::PS_Logic:
      case SMTLIBv2Parser::PS_Memout:
      case SMTLIBv2Parser::PS_Sat:
      case SMTLIBv2Parser::PS_Success:
      case SMTLIBv2Parser::PS_Theory:
      case SMTLIBv2Parser::PS_True:
      case SMTLIBv2Parser::PS_Unknown:
      case SMTLIBv2Parser::PS_Unsupported:
      case SMTLIBv2Parser::PS_Unsat:
      case SMTLIBv2Parser::UndefinedSymbol: {
        enterOuterAlt(_localctx, 1);
        setState(315);
        symbol();
        break;
      }

      case SMTLIBv2Parser::ParOpen: {
        enterOuterAlt(_localctx, 2);
        setState(316);
        match(SMTLIBv2Parser::ParOpen);
        setState(317);
        symbol();
        setState(319); 
        _errHandler->sync(this);
        _la = _input->LA(1);
        do {
          setState(318);
          symbol();
          setState(321); 
          _errHandler->sync(this);
          _la = _input->LA(1);
        } while ((((_la & ~ 0x3fULL) == 0) &&
          ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::QuotedSymbol)
          | (1ULL << SMTLIBv2Parser::PS_Not)
          | (1ULL << SMTLIBv2Parser::PS_Bool)
          | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
          | (1ULL << SMTLIBv2Parser::PS_Error)
          | (1ULL << SMTLIBv2Parser::PS_False)
          | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
          | (1ULL << SMTLIBv2Parser::PS_Incomplete)
          | (1ULL << SMTLIBv2Parser::PS_Logic)
          | (1ULL << SMTLIBv2Parser::PS_Memout)
          | (1ULL << SMTLIBv2Parser::PS_Sat)
          | (1ULL << SMTLIBv2Parser::PS_Success)
          | (1ULL << SMTLIBv2Parser::PS_Theory)
          | (1ULL << SMTLIBv2Parser::PS_True)
          | (1ULL << SMTLIBv2Parser::PS_Unknown)
          | (1ULL << SMTLIBv2Parser::PS_Unsupported)
          | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol);
        setState(323);
        match(SMTLIBv2Parser::ParClose);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Match_caseContext ------------------------------------------------------------------

SMTLIBv2Parser::Match_caseContext::Match_caseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Match_caseContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

SMTLIBv2Parser::PatternContext* SMTLIBv2Parser::Match_caseContext::pattern() {
  return getRuleContext<SMTLIBv2Parser::PatternContext>(0);
}

SMTLIBv2Parser::TermContext* SMTLIBv2Parser::Match_caseContext::term() {
  return getRuleContext<SMTLIBv2Parser::TermContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Match_caseContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::Match_caseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleMatch_case;
}

antlrcpp::Any SMTLIBv2Parser::Match_caseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitMatch_case(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Match_caseContext* SMTLIBv2Parser::match_case() {
  Match_caseContext *_localctx = _tracker.createInstance<Match_caseContext>(_ctx, getState());
  enterRule(_localctx, 50, SMTLIBv2Parser::RuleMatch_case);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(327);
    match(SMTLIBv2Parser::ParOpen);
    setState(328);
    pattern();
    setState(329);
    term();
    setState(330);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- TermContext ------------------------------------------------------------------

SMTLIBv2Parser::TermContext::TermContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::Spec_constantContext* SMTLIBv2Parser::TermContext::spec_constant() {
  return getRuleContext<SMTLIBv2Parser::Spec_constantContext>(0);
}

SMTLIBv2Parser::Qual_identiferContext* SMTLIBv2Parser::TermContext::qual_identifer() {
  return getRuleContext<SMTLIBv2Parser::Qual_identiferContext>(0);
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::TermContext::ParOpen() {
  return getTokens(SMTLIBv2Parser::ParOpen);
}

tree::TerminalNode* SMTLIBv2Parser::TermContext::ParOpen(size_t i) {
  return getToken(SMTLIBv2Parser::ParOpen, i);
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::TermContext::ParClose() {
  return getTokens(SMTLIBv2Parser::ParClose);
}

tree::TerminalNode* SMTLIBv2Parser::TermContext::ParClose(size_t i) {
  return getToken(SMTLIBv2Parser::ParClose, i);
}

std::vector<SMTLIBv2Parser::TermContext *> SMTLIBv2Parser::TermContext::term() {
  return getRuleContexts<SMTLIBv2Parser::TermContext>();
}

SMTLIBv2Parser::TermContext* SMTLIBv2Parser::TermContext::term(size_t i) {
  return getRuleContext<SMTLIBv2Parser::TermContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::TermContext::GRW_Let() {
  return getToken(SMTLIBv2Parser::GRW_Let, 0);
}

std::vector<SMTLIBv2Parser::Var_bindingContext *> SMTLIBv2Parser::TermContext::var_binding() {
  return getRuleContexts<SMTLIBv2Parser::Var_bindingContext>();
}

SMTLIBv2Parser::Var_bindingContext* SMTLIBv2Parser::TermContext::var_binding(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Var_bindingContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::TermContext::GRW_Forall() {
  return getToken(SMTLIBv2Parser::GRW_Forall, 0);
}

std::vector<SMTLIBv2Parser::Sorted_varContext *> SMTLIBv2Parser::TermContext::sorted_var() {
  return getRuleContexts<SMTLIBv2Parser::Sorted_varContext>();
}

SMTLIBv2Parser::Sorted_varContext* SMTLIBv2Parser::TermContext::sorted_var(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Sorted_varContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::TermContext::GRW_Exists() {
  return getToken(SMTLIBv2Parser::GRW_Exists, 0);
}

tree::TerminalNode* SMTLIBv2Parser::TermContext::GRW_Match() {
  return getToken(SMTLIBv2Parser::GRW_Match, 0);
}

std::vector<SMTLIBv2Parser::Match_caseContext *> SMTLIBv2Parser::TermContext::match_case() {
  return getRuleContexts<SMTLIBv2Parser::Match_caseContext>();
}

SMTLIBv2Parser::Match_caseContext* SMTLIBv2Parser::TermContext::match_case(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Match_caseContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::TermContext::GRW_Exclamation() {
  return getToken(SMTLIBv2Parser::GRW_Exclamation, 0);
}

std::vector<SMTLIBv2Parser::AttributeContext *> SMTLIBv2Parser::TermContext::attribute() {
  return getRuleContexts<SMTLIBv2Parser::AttributeContext>();
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::TermContext::attribute(size_t i) {
  return getRuleContext<SMTLIBv2Parser::AttributeContext>(i);
}


size_t SMTLIBv2Parser::TermContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleTerm;
}

antlrcpp::Any SMTLIBv2Parser::TermContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitTerm(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::TermContext* SMTLIBv2Parser::term() {
  TermContext *_localctx = _tracker.createInstance<TermContext>(_ctx, getState());
  enterRule(_localctx, 52, SMTLIBv2Parser::RuleTerm);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(401);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 23, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(332);
      spec_constant();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(333);
      qual_identifer();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(334);
      match(SMTLIBv2Parser::ParOpen);
      setState(335);
      qual_identifer();
      setState(337); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(336);
        term();
        setState(339); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
        | (1ULL << SMTLIBv2Parser::String)
        | (1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || ((((_la - 66) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 66)) & ((1ULL << (SMTLIBv2Parser::Numeral - 66))
        | (1ULL << (SMTLIBv2Parser::Binary - 66))
        | (1ULL << (SMTLIBv2Parser::HexDecimal - 66))
        | (1ULL << (SMTLIBv2Parser::Decimal - 66))
        | (1ULL << (SMTLIBv2Parser::UndefinedSymbol - 66)))) != 0));
      setState(341);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(343);
      match(SMTLIBv2Parser::ParOpen);
      setState(344);
      match(SMTLIBv2Parser::GRW_Let);
      setState(345);
      match(SMTLIBv2Parser::ParOpen);
      setState(347); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(346);
        var_binding();
        setState(349); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(351);
      match(SMTLIBv2Parser::ParClose);
      setState(352);
      term();
      setState(353);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(355);
      match(SMTLIBv2Parser::ParOpen);
      setState(356);
      match(SMTLIBv2Parser::GRW_Forall);
      setState(357);
      match(SMTLIBv2Parser::ParOpen);
      setState(359); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(358);
        sorted_var();
        setState(361); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(363);
      match(SMTLIBv2Parser::ParClose);
      setState(364);
      term();
      setState(365);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(367);
      match(SMTLIBv2Parser::ParOpen);
      setState(368);
      match(SMTLIBv2Parser::GRW_Exists);
      setState(369);
      match(SMTLIBv2Parser::ParOpen);
      setState(371); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(370);
        sorted_var();
        setState(373); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(375);
      match(SMTLIBv2Parser::ParClose);
      setState(376);
      term();
      setState(377);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(379);
      match(SMTLIBv2Parser::ParOpen);
      setState(380);
      match(SMTLIBv2Parser::GRW_Match);
      setState(381);
      term();
      setState(382);
      match(SMTLIBv2Parser::ParOpen);
      setState(384); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(383);
        match_case();
        setState(386); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(388);
      match(SMTLIBv2Parser::ParClose);
      setState(389);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(391);
      match(SMTLIBv2Parser::ParOpen);
      setState(392);
      match(SMTLIBv2Parser::GRW_Exclamation);
      setState(393);
      term();
      setState(395); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(394);
        attribute();
        setState(397); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (((((_la - 70) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 70)) & ((1ULL << (SMTLIBv2Parser::Colon - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Authors - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Category - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Chainable - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Definition - 70))
        | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Extension - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Funs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 70))
        | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Language - 70))
        | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_License - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Named - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Name - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Notes - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Pattern - 70))
        | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Sorts - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Source - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Status - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Theories - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Values - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Version - 70)))) != 0));
      setState(399);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Sort_symbol_declContext ------------------------------------------------------------------

SMTLIBv2Parser::Sort_symbol_declContext::Sort_symbol_declContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Sort_symbol_declContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

SMTLIBv2Parser::IdentifierContext* SMTLIBv2Parser::Sort_symbol_declContext::identifier() {
  return getRuleContext<SMTLIBv2Parser::IdentifierContext>(0);
}

SMTLIBv2Parser::NumeralContext* SMTLIBv2Parser::Sort_symbol_declContext::numeral() {
  return getRuleContext<SMTLIBv2Parser::NumeralContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Sort_symbol_declContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::AttributeContext *> SMTLIBv2Parser::Sort_symbol_declContext::attribute() {
  return getRuleContexts<SMTLIBv2Parser::AttributeContext>();
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::Sort_symbol_declContext::attribute(size_t i) {
  return getRuleContext<SMTLIBv2Parser::AttributeContext>(i);
}


size_t SMTLIBv2Parser::Sort_symbol_declContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleSort_symbol_decl;
}

antlrcpp::Any SMTLIBv2Parser::Sort_symbol_declContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitSort_symbol_decl(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Sort_symbol_declContext* SMTLIBv2Parser::sort_symbol_decl() {
  Sort_symbol_declContext *_localctx = _tracker.createInstance<Sort_symbol_declContext>(_ctx, getState());
  enterRule(_localctx, 54, SMTLIBv2Parser::RuleSort_symbol_decl);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(403);
    match(SMTLIBv2Parser::ParOpen);
    setState(404);
    identifier();
    setState(405);
    numeral();
    setState(409);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (((((_la - 70) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 70)) & ((1ULL << (SMTLIBv2Parser::Colon - 70))
      | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 70))
      | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Authors - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Category - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Chainable - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Definition - 70))
      | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Extension - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Funs - 70))
      | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 70))
      | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 70))
      | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Language - 70))
      | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 70))
      | (1ULL << (SMTLIBv2Parser::PK_License - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Named - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Name - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Notes - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Pattern - 70))
      | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 70))
      | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Sorts - 70))
      | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Source - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Status - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Theories - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Values - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Version - 70)))) != 0)) {
      setState(406);
      attribute();
      setState(411);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(412);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Meta_spec_constantContext ------------------------------------------------------------------

SMTLIBv2Parser::Meta_spec_constantContext::Meta_spec_constantContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Meta_spec_constantContext::GRW_Numeral() {
  return getToken(SMTLIBv2Parser::GRW_Numeral, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Meta_spec_constantContext::GRW_Decimal() {
  return getToken(SMTLIBv2Parser::GRW_Decimal, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Meta_spec_constantContext::GRW_String() {
  return getToken(SMTLIBv2Parser::GRW_String, 0);
}


size_t SMTLIBv2Parser::Meta_spec_constantContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleMeta_spec_constant;
}

antlrcpp::Any SMTLIBv2Parser::Meta_spec_constantContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitMeta_spec_constant(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Meta_spec_constantContext* SMTLIBv2Parser::meta_spec_constant() {
  Meta_spec_constantContext *_localctx = _tracker.createInstance<Meta_spec_constantContext>(_ctx, getState());
  enterRule(_localctx, 56, SMTLIBv2Parser::RuleMeta_spec_constant);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(414);
    _la = _input->LA(1);
    if (!(((((_la - 57) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 57)) & ((1ULL << (SMTLIBv2Parser::GRW_Decimal - 57))
      | (1ULL << (SMTLIBv2Parser::GRW_Numeral - 57))
      | (1ULL << (SMTLIBv2Parser::GRW_String - 57)))) != 0))) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Fun_symbol_declContext ------------------------------------------------------------------

SMTLIBv2Parser::Fun_symbol_declContext::Fun_symbol_declContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Fun_symbol_declContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

SMTLIBv2Parser::Spec_constantContext* SMTLIBv2Parser::Fun_symbol_declContext::spec_constant() {
  return getRuleContext<SMTLIBv2Parser::Spec_constantContext>(0);
}

std::vector<SMTLIBv2Parser::SortContext *> SMTLIBv2Parser::Fun_symbol_declContext::sort() {
  return getRuleContexts<SMTLIBv2Parser::SortContext>();
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::Fun_symbol_declContext::sort(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SortContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::Fun_symbol_declContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::AttributeContext *> SMTLIBv2Parser::Fun_symbol_declContext::attribute() {
  return getRuleContexts<SMTLIBv2Parser::AttributeContext>();
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::Fun_symbol_declContext::attribute(size_t i) {
  return getRuleContext<SMTLIBv2Parser::AttributeContext>(i);
}

SMTLIBv2Parser::Meta_spec_constantContext* SMTLIBv2Parser::Fun_symbol_declContext::meta_spec_constant() {
  return getRuleContext<SMTLIBv2Parser::Meta_spec_constantContext>(0);
}

SMTLIBv2Parser::IdentifierContext* SMTLIBv2Parser::Fun_symbol_declContext::identifier() {
  return getRuleContext<SMTLIBv2Parser::IdentifierContext>(0);
}


size_t SMTLIBv2Parser::Fun_symbol_declContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleFun_symbol_decl;
}

antlrcpp::Any SMTLIBv2Parser::Fun_symbol_declContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitFun_symbol_decl(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Fun_symbol_declContext* SMTLIBv2Parser::fun_symbol_decl() {
  Fun_symbol_declContext *_localctx = _tracker.createInstance<Fun_symbol_declContext>(_ctx, getState());
  enterRule(_localctx, 58, SMTLIBv2Parser::RuleFun_symbol_decl);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(453);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 29, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(416);
      match(SMTLIBv2Parser::ParOpen);
      setState(417);
      spec_constant();
      setState(418);
      sort();
      setState(422);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (((((_la - 70) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 70)) & ((1ULL << (SMTLIBv2Parser::Colon - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Authors - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Category - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Chainable - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Definition - 70))
        | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Extension - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Funs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 70))
        | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Language - 70))
        | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_License - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Named - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Name - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Notes - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Pattern - 70))
        | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Sorts - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Source - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Status - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Theories - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Values - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Version - 70)))) != 0)) {
        setState(419);
        attribute();
        setState(424);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(425);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(427);
      match(SMTLIBv2Parser::ParOpen);
      setState(428);
      meta_spec_constant();
      setState(429);
      sort();
      setState(433);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (((((_la - 70) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 70)) & ((1ULL << (SMTLIBv2Parser::Colon - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Authors - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Category - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Chainable - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Definition - 70))
        | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Extension - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Funs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 70))
        | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Language - 70))
        | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_License - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Named - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Name - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Notes - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Pattern - 70))
        | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Sorts - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Source - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Status - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Theories - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Values - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Version - 70)))) != 0)) {
        setState(430);
        attribute();
        setState(435);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(436);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(438);
      match(SMTLIBv2Parser::ParOpen);
      setState(439);
      identifier();
      setState(441); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(440);
        sort();
        setState(443); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
        | (1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol);
      setState(448);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (((((_la - 70) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 70)) & ((1ULL << (SMTLIBv2Parser::Colon - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Authors - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Category - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Chainable - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Definition - 70))
        | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Extension - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Funs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 70))
        | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Language - 70))
        | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_License - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Named - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Name - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Notes - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Pattern - 70))
        | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Sorts - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Source - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Status - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Theories - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Values - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Version - 70)))) != 0)) {
        setState(445);
        attribute();
        setState(450);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(451);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Par_fun_symbol_declContext ------------------------------------------------------------------

SMTLIBv2Parser::Par_fun_symbol_declContext::Par_fun_symbol_declContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::Fun_symbol_declContext* SMTLIBv2Parser::Par_fun_symbol_declContext::fun_symbol_decl() {
  return getRuleContext<SMTLIBv2Parser::Fun_symbol_declContext>(0);
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::Par_fun_symbol_declContext::ParOpen() {
  return getTokens(SMTLIBv2Parser::ParOpen);
}

tree::TerminalNode* SMTLIBv2Parser::Par_fun_symbol_declContext::ParOpen(size_t i) {
  return getToken(SMTLIBv2Parser::ParOpen, i);
}

tree::TerminalNode* SMTLIBv2Parser::Par_fun_symbol_declContext::GRW_Par() {
  return getToken(SMTLIBv2Parser::GRW_Par, 0);
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::Par_fun_symbol_declContext::ParClose() {
  return getTokens(SMTLIBv2Parser::ParClose);
}

tree::TerminalNode* SMTLIBv2Parser::Par_fun_symbol_declContext::ParClose(size_t i) {
  return getToken(SMTLIBv2Parser::ParClose, i);
}

SMTLIBv2Parser::IdentifierContext* SMTLIBv2Parser::Par_fun_symbol_declContext::identifier() {
  return getRuleContext<SMTLIBv2Parser::IdentifierContext>(0);
}

std::vector<SMTLIBv2Parser::SymbolContext *> SMTLIBv2Parser::Par_fun_symbol_declContext::symbol() {
  return getRuleContexts<SMTLIBv2Parser::SymbolContext>();
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Par_fun_symbol_declContext::symbol(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(i);
}

std::vector<SMTLIBv2Parser::SortContext *> SMTLIBv2Parser::Par_fun_symbol_declContext::sort() {
  return getRuleContexts<SMTLIBv2Parser::SortContext>();
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::Par_fun_symbol_declContext::sort(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SortContext>(i);
}

std::vector<SMTLIBv2Parser::AttributeContext *> SMTLIBv2Parser::Par_fun_symbol_declContext::attribute() {
  return getRuleContexts<SMTLIBv2Parser::AttributeContext>();
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::Par_fun_symbol_declContext::attribute(size_t i) {
  return getRuleContext<SMTLIBv2Parser::AttributeContext>(i);
}


size_t SMTLIBv2Parser::Par_fun_symbol_declContext::getRuleIndex() const {
  return SMTLIBv2Parser::RulePar_fun_symbol_decl;
}

antlrcpp::Any SMTLIBv2Parser::Par_fun_symbol_declContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitPar_fun_symbol_decl(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Par_fun_symbol_declContext* SMTLIBv2Parser::par_fun_symbol_decl() {
  Par_fun_symbol_declContext *_localctx = _tracker.createInstance<Par_fun_symbol_declContext>(_ctx, getState());
  enterRule(_localctx, 60, SMTLIBv2Parser::RulePar_fun_symbol_decl);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(481);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 33, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(455);
      fun_symbol_decl();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(456);
      match(SMTLIBv2Parser::ParOpen);
      setState(457);
      match(SMTLIBv2Parser::GRW_Par);
      setState(458);
      match(SMTLIBv2Parser::ParOpen);
      setState(460); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(459);
        symbol();
        setState(462); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol);
      setState(464);
      match(SMTLIBv2Parser::ParClose);
      setState(465);
      match(SMTLIBv2Parser::ParOpen);
      setState(466);
      identifier();
      setState(468); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(467);
        sort();
        setState(470); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
        | (1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol);
      setState(475);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while (((((_la - 70) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 70)) & ((1ULL << (SMTLIBv2Parser::Colon - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 70))
        | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Authors - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Category - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Chainable - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Definition - 70))
        | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Extension - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Funs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 70))
        | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Language - 70))
        | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_License - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Named - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Name - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Notes - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Pattern - 70))
        | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 70))
        | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 70))
        | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Sorts - 70))
        | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Source - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Status - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Theories - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Values - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 70))
        | (1ULL << (SMTLIBv2Parser::PK_Version - 70)))) != 0)) {
        setState(472);
        attribute();
        setState(477);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(478);
      match(SMTLIBv2Parser::ParClose);
      setState(479);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Theory_attributeContext ------------------------------------------------------------------

SMTLIBv2Parser::Theory_attributeContext::Theory_attributeContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Theory_attributeContext::PK_Sorts() {
  return getToken(SMTLIBv2Parser::PK_Sorts, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_attributeContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_attributeContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::Sort_symbol_declContext *> SMTLIBv2Parser::Theory_attributeContext::sort_symbol_decl() {
  return getRuleContexts<SMTLIBv2Parser::Sort_symbol_declContext>();
}

SMTLIBv2Parser::Sort_symbol_declContext* SMTLIBv2Parser::Theory_attributeContext::sort_symbol_decl(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Sort_symbol_declContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_attributeContext::PK_Funs() {
  return getToken(SMTLIBv2Parser::PK_Funs, 0);
}

std::vector<SMTLIBv2Parser::Par_fun_symbol_declContext *> SMTLIBv2Parser::Theory_attributeContext::par_fun_symbol_decl() {
  return getRuleContexts<SMTLIBv2Parser::Par_fun_symbol_declContext>();
}

SMTLIBv2Parser::Par_fun_symbol_declContext* SMTLIBv2Parser::Theory_attributeContext::par_fun_symbol_decl(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Par_fun_symbol_declContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_attributeContext::PK_SortsDescription() {
  return getToken(SMTLIBv2Parser::PK_SortsDescription, 0);
}

SMTLIBv2Parser::StringContext* SMTLIBv2Parser::Theory_attributeContext::string() {
  return getRuleContext<SMTLIBv2Parser::StringContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_attributeContext::PK_FunsDescription() {
  return getToken(SMTLIBv2Parser::PK_FunsDescription, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_attributeContext::PK_Definition() {
  return getToken(SMTLIBv2Parser::PK_Definition, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_attributeContext::PK_Values() {
  return getToken(SMTLIBv2Parser::PK_Values, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_attributeContext::PK_Notes() {
  return getToken(SMTLIBv2Parser::PK_Notes, 0);
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::Theory_attributeContext::attribute() {
  return getRuleContext<SMTLIBv2Parser::AttributeContext>(0);
}


size_t SMTLIBv2Parser::Theory_attributeContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleTheory_attribute;
}

antlrcpp::Any SMTLIBv2Parser::Theory_attributeContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitTheory_attribute(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Theory_attributeContext* SMTLIBv2Parser::theory_attribute() {
  Theory_attributeContext *_localctx = _tracker.createInstance<Theory_attributeContext>(_ctx, getState());
  enterRule(_localctx, 62, SMTLIBv2Parser::RuleTheory_attribute);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(512);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 36, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(483);
      match(SMTLIBv2Parser::PK_Sorts);
      setState(484);
      match(SMTLIBv2Parser::ParOpen);
      setState(486); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(485);
        sort_symbol_decl();
        setState(488); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(490);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(492);
      match(SMTLIBv2Parser::PK_Funs);
      setState(493);
      match(SMTLIBv2Parser::ParOpen);
      setState(495); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(494);
        par_fun_symbol_decl();
        setState(497); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(499);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(501);
      match(SMTLIBv2Parser::PK_SortsDescription);
      setState(502);
      string();
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(503);
      match(SMTLIBv2Parser::PK_FunsDescription);
      setState(504);
      string();
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(505);
      match(SMTLIBv2Parser::PK_Definition);
      setState(506);
      string();
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(507);
      match(SMTLIBv2Parser::PK_Values);
      setState(508);
      string();
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(509);
      match(SMTLIBv2Parser::PK_Notes);
      setState(510);
      string();
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(511);
      attribute();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Theory_declContext ------------------------------------------------------------------

SMTLIBv2Parser::Theory_declContext::Theory_declContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Theory_declContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_declContext::PS_Theory() {
  return getToken(SMTLIBv2Parser::PS_Theory, 0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Theory_declContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Theory_declContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::Theory_attributeContext *> SMTLIBv2Parser::Theory_declContext::theory_attribute() {
  return getRuleContexts<SMTLIBv2Parser::Theory_attributeContext>();
}

SMTLIBv2Parser::Theory_attributeContext* SMTLIBv2Parser::Theory_declContext::theory_attribute(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Theory_attributeContext>(i);
}


size_t SMTLIBv2Parser::Theory_declContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleTheory_decl;
}

antlrcpp::Any SMTLIBv2Parser::Theory_declContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitTheory_decl(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Theory_declContext* SMTLIBv2Parser::theory_decl() {
  Theory_declContext *_localctx = _tracker.createInstance<Theory_declContext>(_ctx, getState());
  enterRule(_localctx, 64, SMTLIBv2Parser::RuleTheory_decl);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(514);
    match(SMTLIBv2Parser::ParOpen);
    setState(515);
    match(SMTLIBv2Parser::PS_Theory);
    setState(516);
    symbol();
    setState(518); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(517);
      theory_attribute();
      setState(520); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (((((_la - 70) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 70)) & ((1ULL << (SMTLIBv2Parser::Colon - 70))
      | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 70))
      | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Authors - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Category - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Chainable - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Definition - 70))
      | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Extension - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Funs - 70))
      | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 70))
      | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 70))
      | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Language - 70))
      | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 70))
      | (1ULL << (SMTLIBv2Parser::PK_License - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Named - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Name - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Notes - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Pattern - 70))
      | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 70))
      | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Sorts - 70))
      | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Source - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Status - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Theories - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Values - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Version - 70)))) != 0));
    setState(522);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Logic_attribueContext ------------------------------------------------------------------

SMTLIBv2Parser::Logic_attribueContext::Logic_attribueContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Logic_attribueContext::PK_Theories() {
  return getToken(SMTLIBv2Parser::PK_Theories, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Logic_attribueContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Logic_attribueContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::SymbolContext *> SMTLIBv2Parser::Logic_attribueContext::symbol() {
  return getRuleContexts<SMTLIBv2Parser::SymbolContext>();
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Logic_attribueContext::symbol(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::Logic_attribueContext::PK_Language() {
  return getToken(SMTLIBv2Parser::PK_Language, 0);
}

SMTLIBv2Parser::StringContext* SMTLIBv2Parser::Logic_attribueContext::string() {
  return getRuleContext<SMTLIBv2Parser::StringContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Logic_attribueContext::PK_Extension() {
  return getToken(SMTLIBv2Parser::PK_Extension, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Logic_attribueContext::PK_Values() {
  return getToken(SMTLIBv2Parser::PK_Values, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Logic_attribueContext::PK_Notes() {
  return getToken(SMTLIBv2Parser::PK_Notes, 0);
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::Logic_attribueContext::attribute() {
  return getRuleContext<SMTLIBv2Parser::AttributeContext>(0);
}


size_t SMTLIBv2Parser::Logic_attribueContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleLogic_attribue;
}

antlrcpp::Any SMTLIBv2Parser::Logic_attribueContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitLogic_attribue(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Logic_attribueContext* SMTLIBv2Parser::logic_attribue() {
  Logic_attribueContext *_localctx = _tracker.createInstance<Logic_attribueContext>(_ctx, getState());
  enterRule(_localctx, 66, SMTLIBv2Parser::RuleLogic_attribue);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(542);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 39, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(524);
      match(SMTLIBv2Parser::PK_Theories);
      setState(525);
      match(SMTLIBv2Parser::ParOpen);
      setState(527); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(526);
        symbol();
        setState(529); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol);
      setState(531);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(533);
      match(SMTLIBv2Parser::PK_Language);
      setState(534);
      string();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(535);
      match(SMTLIBv2Parser::PK_Extension);
      setState(536);
      string();
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(537);
      match(SMTLIBv2Parser::PK_Values);
      setState(538);
      string();
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(539);
      match(SMTLIBv2Parser::PK_Notes);
      setState(540);
      string();
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(541);
      attribute();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- LogicContext ------------------------------------------------------------------

SMTLIBv2Parser::LogicContext::LogicContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::LogicContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::LogicContext::PS_Logic() {
  return getToken(SMTLIBv2Parser::PS_Logic, 0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::LogicContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::LogicContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::Logic_attribueContext *> SMTLIBv2Parser::LogicContext::logic_attribue() {
  return getRuleContexts<SMTLIBv2Parser::Logic_attribueContext>();
}

SMTLIBv2Parser::Logic_attribueContext* SMTLIBv2Parser::LogicContext::logic_attribue(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Logic_attribueContext>(i);
}


size_t SMTLIBv2Parser::LogicContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleLogic;
}

antlrcpp::Any SMTLIBv2Parser::LogicContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitLogic(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::LogicContext* SMTLIBv2Parser::logic() {
  LogicContext *_localctx = _tracker.createInstance<LogicContext>(_ctx, getState());
  enterRule(_localctx, 68, SMTLIBv2Parser::RuleLogic);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(544);
    match(SMTLIBv2Parser::ParOpen);
    setState(545);
    match(SMTLIBv2Parser::PS_Logic);
    setState(546);
    symbol();
    setState(548); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(547);
      logic_attribue();
      setState(550); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (((((_la - 70) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 70)) & ((1ULL << (SMTLIBv2Parser::Colon - 70))
      | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 70))
      | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Authors - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Category - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Chainable - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Definition - 70))
      | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Extension - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Funs - 70))
      | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 70))
      | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 70))
      | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Language - 70))
      | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 70))
      | (1ULL << (SMTLIBv2Parser::PK_License - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Named - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Name - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Notes - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Pattern - 70))
      | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 70))
      | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Sorts - 70))
      | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Source - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Status - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Theories - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Values - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Version - 70)))) != 0));
    setState(552);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Sort_decContext ------------------------------------------------------------------

SMTLIBv2Parser::Sort_decContext::Sort_decContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Sort_decContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Sort_decContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

SMTLIBv2Parser::NumeralContext* SMTLIBv2Parser::Sort_decContext::numeral() {
  return getRuleContext<SMTLIBv2Parser::NumeralContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Sort_decContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::Sort_decContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleSort_dec;
}

antlrcpp::Any SMTLIBv2Parser::Sort_decContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitSort_dec(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Sort_decContext* SMTLIBv2Parser::sort_dec() {
  Sort_decContext *_localctx = _tracker.createInstance<Sort_decContext>(_ctx, getState());
  enterRule(_localctx, 70, SMTLIBv2Parser::RuleSort_dec);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(554);
    match(SMTLIBv2Parser::ParOpen);
    setState(555);
    symbol();
    setState(556);
    numeral();
    setState(557);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Selector_decContext ------------------------------------------------------------------

SMTLIBv2Parser::Selector_decContext::Selector_decContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Selector_decContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Selector_decContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::Selector_decContext::sort() {
  return getRuleContext<SMTLIBv2Parser::SortContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Selector_decContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::Selector_decContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleSelector_dec;
}

antlrcpp::Any SMTLIBv2Parser::Selector_decContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitSelector_dec(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Selector_decContext* SMTLIBv2Parser::selector_dec() {
  Selector_decContext *_localctx = _tracker.createInstance<Selector_decContext>(_ctx, getState());
  enterRule(_localctx, 72, SMTLIBv2Parser::RuleSelector_dec);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(559);
    match(SMTLIBv2Parser::ParOpen);
    setState(560);
    symbol();
    setState(561);
    sort();
    setState(562);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Constructor_decContext ------------------------------------------------------------------

SMTLIBv2Parser::Constructor_decContext::Constructor_decContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Constructor_decContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Constructor_decContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Constructor_decContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::Selector_decContext *> SMTLIBv2Parser::Constructor_decContext::selector_dec() {
  return getRuleContexts<SMTLIBv2Parser::Selector_decContext>();
}

SMTLIBv2Parser::Selector_decContext* SMTLIBv2Parser::Constructor_decContext::selector_dec(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Selector_decContext>(i);
}


size_t SMTLIBv2Parser::Constructor_decContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleConstructor_dec;
}

antlrcpp::Any SMTLIBv2Parser::Constructor_decContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitConstructor_dec(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Constructor_decContext* SMTLIBv2Parser::constructor_dec() {
  Constructor_decContext *_localctx = _tracker.createInstance<Constructor_decContext>(_ctx, getState());
  enterRule(_localctx, 74, SMTLIBv2Parser::RuleConstructor_dec);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(564);
    match(SMTLIBv2Parser::ParOpen);
    setState(565);
    symbol();
    setState(569);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SMTLIBv2Parser::ParOpen) {
      setState(566);
      selector_dec();
      setState(571);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(572);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Datatype_decContext ------------------------------------------------------------------

SMTLIBv2Parser::Datatype_decContext::Datatype_decContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::Datatype_decContext::ParOpen() {
  return getTokens(SMTLIBv2Parser::ParOpen);
}

tree::TerminalNode* SMTLIBv2Parser::Datatype_decContext::ParOpen(size_t i) {
  return getToken(SMTLIBv2Parser::ParOpen, i);
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::Datatype_decContext::ParClose() {
  return getTokens(SMTLIBv2Parser::ParClose);
}

tree::TerminalNode* SMTLIBv2Parser::Datatype_decContext::ParClose(size_t i) {
  return getToken(SMTLIBv2Parser::ParClose, i);
}

std::vector<SMTLIBv2Parser::Constructor_decContext *> SMTLIBv2Parser::Datatype_decContext::constructor_dec() {
  return getRuleContexts<SMTLIBv2Parser::Constructor_decContext>();
}

SMTLIBv2Parser::Constructor_decContext* SMTLIBv2Parser::Datatype_decContext::constructor_dec(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Constructor_decContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::Datatype_decContext::GRW_Par() {
  return getToken(SMTLIBv2Parser::GRW_Par, 0);
}

std::vector<SMTLIBv2Parser::SymbolContext *> SMTLIBv2Parser::Datatype_decContext::symbol() {
  return getRuleContexts<SMTLIBv2Parser::SymbolContext>();
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Datatype_decContext::symbol(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(i);
}


size_t SMTLIBv2Parser::Datatype_decContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleDatatype_dec;
}

antlrcpp::Any SMTLIBv2Parser::Datatype_decContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitDatatype_dec(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Datatype_decContext* SMTLIBv2Parser::datatype_dec() {
  Datatype_decContext *_localctx = _tracker.createInstance<Datatype_decContext>(_ctx, getState());
  enterRule(_localctx, 76, SMTLIBv2Parser::RuleDatatype_dec);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(600);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 45, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(574);
      match(SMTLIBv2Parser::ParOpen);
      setState(576); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(575);
        constructor_dec();
        setState(578); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(580);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(582);
      match(SMTLIBv2Parser::ParOpen);
      setState(583);
      match(SMTLIBv2Parser::GRW_Par);
      setState(584);
      match(SMTLIBv2Parser::ParOpen);
      setState(586); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(585);
        symbol();
        setState(588); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol);
      setState(590);
      match(SMTLIBv2Parser::ParClose);
      setState(591);
      match(SMTLIBv2Parser::ParOpen);
      setState(593); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(592);
        constructor_dec();
        setState(595); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(597);
      match(SMTLIBv2Parser::ParClose);
      setState(598);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Function_decContext ------------------------------------------------------------------

SMTLIBv2Parser::Function_decContext::Function_decContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::Function_decContext::ParOpen() {
  return getTokens(SMTLIBv2Parser::ParOpen);
}

tree::TerminalNode* SMTLIBv2Parser::Function_decContext::ParOpen(size_t i) {
  return getToken(SMTLIBv2Parser::ParOpen, i);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Function_decContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::Function_decContext::ParClose() {
  return getTokens(SMTLIBv2Parser::ParClose);
}

tree::TerminalNode* SMTLIBv2Parser::Function_decContext::ParClose(size_t i) {
  return getToken(SMTLIBv2Parser::ParClose, i);
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::Function_decContext::sort() {
  return getRuleContext<SMTLIBv2Parser::SortContext>(0);
}

std::vector<SMTLIBv2Parser::Sorted_varContext *> SMTLIBv2Parser::Function_decContext::sorted_var() {
  return getRuleContexts<SMTLIBv2Parser::Sorted_varContext>();
}

SMTLIBv2Parser::Sorted_varContext* SMTLIBv2Parser::Function_decContext::sorted_var(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Sorted_varContext>(i);
}


size_t SMTLIBv2Parser::Function_decContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleFunction_dec;
}

antlrcpp::Any SMTLIBv2Parser::Function_decContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitFunction_dec(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Function_decContext* SMTLIBv2Parser::function_dec() {
  Function_decContext *_localctx = _tracker.createInstance<Function_decContext>(_ctx, getState());
  enterRule(_localctx, 78, SMTLIBv2Parser::RuleFunction_dec);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(602);
    match(SMTLIBv2Parser::ParOpen);
    setState(603);
    symbol();
    setState(604);
    match(SMTLIBv2Parser::ParOpen);
    setState(608);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SMTLIBv2Parser::ParOpen) {
      setState(605);
      sorted_var();
      setState(610);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(611);
    match(SMTLIBv2Parser::ParClose);
    setState(612);
    sort();
    setState(613);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Function_defContext ------------------------------------------------------------------

SMTLIBv2Parser::Function_defContext::Function_defContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Function_defContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Function_defContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Function_defContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::Function_defContext::sort() {
  return getRuleContext<SMTLIBv2Parser::SortContext>(0);
}

SMTLIBv2Parser::TermContext* SMTLIBv2Parser::Function_defContext::term() {
  return getRuleContext<SMTLIBv2Parser::TermContext>(0);
}

std::vector<SMTLIBv2Parser::Sorted_varContext *> SMTLIBv2Parser::Function_defContext::sorted_var() {
  return getRuleContexts<SMTLIBv2Parser::Sorted_varContext>();
}

SMTLIBv2Parser::Sorted_varContext* SMTLIBv2Parser::Function_defContext::sorted_var(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Sorted_varContext>(i);
}


size_t SMTLIBv2Parser::Function_defContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleFunction_def;
}

antlrcpp::Any SMTLIBv2Parser::Function_defContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitFunction_def(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Function_defContext* SMTLIBv2Parser::function_def() {
  Function_defContext *_localctx = _tracker.createInstance<Function_defContext>(_ctx, getState());
  enterRule(_localctx, 80, SMTLIBv2Parser::RuleFunction_def);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(615);
    symbol();
    setState(616);
    match(SMTLIBv2Parser::ParOpen);
    setState(620);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SMTLIBv2Parser::ParOpen) {
      setState(617);
      sorted_var();
      setState(622);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(623);
    match(SMTLIBv2Parser::ParClose);
    setState(624);
    sort();
    setState(625);
    term();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Prop_literalContext ------------------------------------------------------------------

SMTLIBv2Parser::Prop_literalContext::Prop_literalContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Prop_literalContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Prop_literalContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Prop_literalContext::PS_Not() {
  return getToken(SMTLIBv2Parser::PS_Not, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Prop_literalContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::Prop_literalContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleProp_literal;
}

antlrcpp::Any SMTLIBv2Parser::Prop_literalContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitProp_literal(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Prop_literalContext* SMTLIBv2Parser::prop_literal() {
  Prop_literalContext *_localctx = _tracker.createInstance<Prop_literalContext>(_ctx, getState());
  enterRule(_localctx, 82, SMTLIBv2Parser::RuleProp_literal);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(633);
    _errHandler->sync(this);
    switch (_input->LA(1)) {
      case SMTLIBv2Parser::QuotedSymbol:
      case SMTLIBv2Parser::PS_Not:
      case SMTLIBv2Parser::PS_Bool:
      case SMTLIBv2Parser::PS_ContinuedExecution:
      case SMTLIBv2Parser::PS_Error:
      case SMTLIBv2Parser::PS_False:
      case SMTLIBv2Parser::PS_ImmediateExit:
      case SMTLIBv2Parser::PS_Incomplete:
      case SMTLIBv2Parser::PS_Logic:
      case SMTLIBv2Parser::PS_Memout:
      case SMTLIBv2Parser::PS_Sat:
      case SMTLIBv2Parser::PS_Success:
      case SMTLIBv2Parser::PS_Theory:
      case SMTLIBv2Parser::PS_True:
      case SMTLIBv2Parser::PS_Unknown:
      case SMTLIBv2Parser::PS_Unsupported:
      case SMTLIBv2Parser::PS_Unsat:
      case SMTLIBv2Parser::UndefinedSymbol: {
        enterOuterAlt(_localctx, 1);
        setState(627);
        symbol();
        break;
      }

      case SMTLIBv2Parser::ParOpen: {
        enterOuterAlt(_localctx, 2);
        setState(628);
        match(SMTLIBv2Parser::ParOpen);
        setState(629);
        match(SMTLIBv2Parser::PS_Not);
        setState(630);
        symbol();
        setState(631);
        match(SMTLIBv2Parser::ParClose);
        break;
      }

    default:
      throw NoViableAltException(this);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- ScriptContext ------------------------------------------------------------------

SMTLIBv2Parser::ScriptContext::ScriptContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<SMTLIBv2Parser::CommandContext *> SMTLIBv2Parser::ScriptContext::command() {
  return getRuleContexts<SMTLIBv2Parser::CommandContext>();
}

SMTLIBv2Parser::CommandContext* SMTLIBv2Parser::ScriptContext::command(size_t i) {
  return getRuleContext<SMTLIBv2Parser::CommandContext>(i);
}


size_t SMTLIBv2Parser::ScriptContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleScript;
}

antlrcpp::Any SMTLIBv2Parser::ScriptContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitScript(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::ScriptContext* SMTLIBv2Parser::script() {
  ScriptContext *_localctx = _tracker.createInstance<ScriptContext>(_ctx, getState());
  enterRule(_localctx, 84, SMTLIBv2Parser::RuleScript);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(638);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SMTLIBv2Parser::ParOpen) {
      setState(635);
      command();
      setState(640);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_assertContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_assertContext::Cmd_assertContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_assertContext::CMD_Assert() {
  return getToken(SMTLIBv2Parser::CMD_Assert, 0);
}


size_t SMTLIBv2Parser::Cmd_assertContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_assert;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_assertContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_assert(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_assertContext* SMTLIBv2Parser::cmd_assert() {
  Cmd_assertContext *_localctx = _tracker.createInstance<Cmd_assertContext>(_ctx, getState());
  enterRule(_localctx, 86, SMTLIBv2Parser::RuleCmd_assert);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(641);
    match(SMTLIBv2Parser::CMD_Assert);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_checkSatContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_checkSatContext::Cmd_checkSatContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_checkSatContext::CMD_CheckSat() {
  return getToken(SMTLIBv2Parser::CMD_CheckSat, 0);
}


size_t SMTLIBv2Parser::Cmd_checkSatContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_checkSat;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_checkSatContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_checkSat(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_checkSatContext* SMTLIBv2Parser::cmd_checkSat() {
  Cmd_checkSatContext *_localctx = _tracker.createInstance<Cmd_checkSatContext>(_ctx, getState());
  enterRule(_localctx, 88, SMTLIBv2Parser::RuleCmd_checkSat);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(643);
    match(SMTLIBv2Parser::CMD_CheckSat);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_checkSatAssumingContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_checkSatAssumingContext::Cmd_checkSatAssumingContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_checkSatAssumingContext::CMD_CheckSatAssuming() {
  return getToken(SMTLIBv2Parser::CMD_CheckSatAssuming, 0);
}


size_t SMTLIBv2Parser::Cmd_checkSatAssumingContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_checkSatAssuming;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_checkSatAssumingContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_checkSatAssuming(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_checkSatAssumingContext* SMTLIBv2Parser::cmd_checkSatAssuming() {
  Cmd_checkSatAssumingContext *_localctx = _tracker.createInstance<Cmd_checkSatAssumingContext>(_ctx, getState());
  enterRule(_localctx, 90, SMTLIBv2Parser::RuleCmd_checkSatAssuming);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(645);
    match(SMTLIBv2Parser::CMD_CheckSatAssuming);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_declareConstContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_declareConstContext::Cmd_declareConstContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_declareConstContext::CMD_DeclareConst() {
  return getToken(SMTLIBv2Parser::CMD_DeclareConst, 0);
}


size_t SMTLIBv2Parser::Cmd_declareConstContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_declareConst;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_declareConstContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_declareConst(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_declareConstContext* SMTLIBv2Parser::cmd_declareConst() {
  Cmd_declareConstContext *_localctx = _tracker.createInstance<Cmd_declareConstContext>(_ctx, getState());
  enterRule(_localctx, 92, SMTLIBv2Parser::RuleCmd_declareConst);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(647);
    match(SMTLIBv2Parser::CMD_DeclareConst);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_declareDatatypeContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_declareDatatypeContext::Cmd_declareDatatypeContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_declareDatatypeContext::CMD_DeclareDatatype() {
  return getToken(SMTLIBv2Parser::CMD_DeclareDatatype, 0);
}


size_t SMTLIBv2Parser::Cmd_declareDatatypeContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_declareDatatype;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_declareDatatypeContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_declareDatatype(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_declareDatatypeContext* SMTLIBv2Parser::cmd_declareDatatype() {
  Cmd_declareDatatypeContext *_localctx = _tracker.createInstance<Cmd_declareDatatypeContext>(_ctx, getState());
  enterRule(_localctx, 94, SMTLIBv2Parser::RuleCmd_declareDatatype);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(649);
    match(SMTLIBv2Parser::CMD_DeclareDatatype);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_declareDatatypesContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_declareDatatypesContext::Cmd_declareDatatypesContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_declareDatatypesContext::CMD_DeclareDatatypes() {
  return getToken(SMTLIBv2Parser::CMD_DeclareDatatypes, 0);
}


size_t SMTLIBv2Parser::Cmd_declareDatatypesContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_declareDatatypes;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_declareDatatypesContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_declareDatatypes(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_declareDatatypesContext* SMTLIBv2Parser::cmd_declareDatatypes() {
  Cmd_declareDatatypesContext *_localctx = _tracker.createInstance<Cmd_declareDatatypesContext>(_ctx, getState());
  enterRule(_localctx, 96, SMTLIBv2Parser::RuleCmd_declareDatatypes);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(651);
    match(SMTLIBv2Parser::CMD_DeclareDatatypes);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_declareFunContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_declareFunContext::Cmd_declareFunContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_declareFunContext::CMD_DeclareFun() {
  return getToken(SMTLIBv2Parser::CMD_DeclareFun, 0);
}


size_t SMTLIBv2Parser::Cmd_declareFunContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_declareFun;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_declareFunContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_declareFun(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_declareFunContext* SMTLIBv2Parser::cmd_declareFun() {
  Cmd_declareFunContext *_localctx = _tracker.createInstance<Cmd_declareFunContext>(_ctx, getState());
  enterRule(_localctx, 98, SMTLIBv2Parser::RuleCmd_declareFun);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(653);
    match(SMTLIBv2Parser::CMD_DeclareFun);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_declareSortContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_declareSortContext::Cmd_declareSortContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_declareSortContext::CMD_DeclareSort() {
  return getToken(SMTLIBv2Parser::CMD_DeclareSort, 0);
}


size_t SMTLIBv2Parser::Cmd_declareSortContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_declareSort;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_declareSortContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_declareSort(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_declareSortContext* SMTLIBv2Parser::cmd_declareSort() {
  Cmd_declareSortContext *_localctx = _tracker.createInstance<Cmd_declareSortContext>(_ctx, getState());
  enterRule(_localctx, 100, SMTLIBv2Parser::RuleCmd_declareSort);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(655);
    match(SMTLIBv2Parser::CMD_DeclareSort);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_defineFunContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_defineFunContext::Cmd_defineFunContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_defineFunContext::CMD_DefineFun() {
  return getToken(SMTLIBv2Parser::CMD_DefineFun, 0);
}


size_t SMTLIBv2Parser::Cmd_defineFunContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_defineFun;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_defineFunContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_defineFun(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_defineFunContext* SMTLIBv2Parser::cmd_defineFun() {
  Cmd_defineFunContext *_localctx = _tracker.createInstance<Cmd_defineFunContext>(_ctx, getState());
  enterRule(_localctx, 102, SMTLIBv2Parser::RuleCmd_defineFun);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(657);
    match(SMTLIBv2Parser::CMD_DefineFun);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_defineFunRecContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_defineFunRecContext::Cmd_defineFunRecContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_defineFunRecContext::CMD_DefineFunRec() {
  return getToken(SMTLIBv2Parser::CMD_DefineFunRec, 0);
}


size_t SMTLIBv2Parser::Cmd_defineFunRecContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_defineFunRec;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_defineFunRecContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_defineFunRec(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_defineFunRecContext* SMTLIBv2Parser::cmd_defineFunRec() {
  Cmd_defineFunRecContext *_localctx = _tracker.createInstance<Cmd_defineFunRecContext>(_ctx, getState());
  enterRule(_localctx, 104, SMTLIBv2Parser::RuleCmd_defineFunRec);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(659);
    match(SMTLIBv2Parser::CMD_DefineFunRec);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_defineFunsRecContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_defineFunsRecContext::Cmd_defineFunsRecContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_defineFunsRecContext::CMD_DefineFunsRec() {
  return getToken(SMTLIBv2Parser::CMD_DefineFunsRec, 0);
}


size_t SMTLIBv2Parser::Cmd_defineFunsRecContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_defineFunsRec;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_defineFunsRecContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_defineFunsRec(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_defineFunsRecContext* SMTLIBv2Parser::cmd_defineFunsRec() {
  Cmd_defineFunsRecContext *_localctx = _tracker.createInstance<Cmd_defineFunsRecContext>(_ctx, getState());
  enterRule(_localctx, 106, SMTLIBv2Parser::RuleCmd_defineFunsRec);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(661);
    match(SMTLIBv2Parser::CMD_DefineFunsRec);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_defineSortContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_defineSortContext::Cmd_defineSortContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_defineSortContext::CMD_DefineSort() {
  return getToken(SMTLIBv2Parser::CMD_DefineSort, 0);
}


size_t SMTLIBv2Parser::Cmd_defineSortContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_defineSort;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_defineSortContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_defineSort(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_defineSortContext* SMTLIBv2Parser::cmd_defineSort() {
  Cmd_defineSortContext *_localctx = _tracker.createInstance<Cmd_defineSortContext>(_ctx, getState());
  enterRule(_localctx, 108, SMTLIBv2Parser::RuleCmd_defineSort);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(663);
    match(SMTLIBv2Parser::CMD_DefineSort);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_echoContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_echoContext::Cmd_echoContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_echoContext::CMD_Echo() {
  return getToken(SMTLIBv2Parser::CMD_Echo, 0);
}


size_t SMTLIBv2Parser::Cmd_echoContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_echo;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_echoContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_echo(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_echoContext* SMTLIBv2Parser::cmd_echo() {
  Cmd_echoContext *_localctx = _tracker.createInstance<Cmd_echoContext>(_ctx, getState());
  enterRule(_localctx, 110, SMTLIBv2Parser::RuleCmd_echo);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(665);
    match(SMTLIBv2Parser::CMD_Echo);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_exitContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_exitContext::Cmd_exitContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_exitContext::CMD_Exit() {
  return getToken(SMTLIBv2Parser::CMD_Exit, 0);
}


size_t SMTLIBv2Parser::Cmd_exitContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_exit;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_exitContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_exit(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_exitContext* SMTLIBv2Parser::cmd_exit() {
  Cmd_exitContext *_localctx = _tracker.createInstance<Cmd_exitContext>(_ctx, getState());
  enterRule(_localctx, 112, SMTLIBv2Parser::RuleCmd_exit);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(667);
    match(SMTLIBv2Parser::CMD_Exit);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_getAssertionsContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_getAssertionsContext::Cmd_getAssertionsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_getAssertionsContext::CMD_GetAssertions() {
  return getToken(SMTLIBv2Parser::CMD_GetAssertions, 0);
}


size_t SMTLIBv2Parser::Cmd_getAssertionsContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_getAssertions;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_getAssertionsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_getAssertions(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_getAssertionsContext* SMTLIBv2Parser::cmd_getAssertions() {
  Cmd_getAssertionsContext *_localctx = _tracker.createInstance<Cmd_getAssertionsContext>(_ctx, getState());
  enterRule(_localctx, 114, SMTLIBv2Parser::RuleCmd_getAssertions);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(669);
    match(SMTLIBv2Parser::CMD_GetAssertions);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_getAssignmentContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_getAssignmentContext::Cmd_getAssignmentContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_getAssignmentContext::CMD_GetAssignment() {
  return getToken(SMTLIBv2Parser::CMD_GetAssignment, 0);
}


size_t SMTLIBv2Parser::Cmd_getAssignmentContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_getAssignment;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_getAssignmentContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_getAssignment(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_getAssignmentContext* SMTLIBv2Parser::cmd_getAssignment() {
  Cmd_getAssignmentContext *_localctx = _tracker.createInstance<Cmd_getAssignmentContext>(_ctx, getState());
  enterRule(_localctx, 116, SMTLIBv2Parser::RuleCmd_getAssignment);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(671);
    match(SMTLIBv2Parser::CMD_GetAssignment);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_getInfoContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_getInfoContext::Cmd_getInfoContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_getInfoContext::CMD_GetInfo() {
  return getToken(SMTLIBv2Parser::CMD_GetInfo, 0);
}


size_t SMTLIBv2Parser::Cmd_getInfoContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_getInfo;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_getInfoContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_getInfo(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_getInfoContext* SMTLIBv2Parser::cmd_getInfo() {
  Cmd_getInfoContext *_localctx = _tracker.createInstance<Cmd_getInfoContext>(_ctx, getState());
  enterRule(_localctx, 118, SMTLIBv2Parser::RuleCmd_getInfo);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(673);
    match(SMTLIBv2Parser::CMD_GetInfo);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_getModelContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_getModelContext::Cmd_getModelContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_getModelContext::CMD_GetModel() {
  return getToken(SMTLIBv2Parser::CMD_GetModel, 0);
}


size_t SMTLIBv2Parser::Cmd_getModelContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_getModel;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_getModelContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_getModel(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_getModelContext* SMTLIBv2Parser::cmd_getModel() {
  Cmd_getModelContext *_localctx = _tracker.createInstance<Cmd_getModelContext>(_ctx, getState());
  enterRule(_localctx, 120, SMTLIBv2Parser::RuleCmd_getModel);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(675);
    match(SMTLIBv2Parser::CMD_GetModel);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_getOptionContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_getOptionContext::Cmd_getOptionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_getOptionContext::CMD_GetOption() {
  return getToken(SMTLIBv2Parser::CMD_GetOption, 0);
}


size_t SMTLIBv2Parser::Cmd_getOptionContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_getOption;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_getOptionContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_getOption(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_getOptionContext* SMTLIBv2Parser::cmd_getOption() {
  Cmd_getOptionContext *_localctx = _tracker.createInstance<Cmd_getOptionContext>(_ctx, getState());
  enterRule(_localctx, 122, SMTLIBv2Parser::RuleCmd_getOption);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(677);
    match(SMTLIBv2Parser::CMD_GetOption);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_getProofContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_getProofContext::Cmd_getProofContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_getProofContext::CMD_GetProof() {
  return getToken(SMTLIBv2Parser::CMD_GetProof, 0);
}


size_t SMTLIBv2Parser::Cmd_getProofContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_getProof;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_getProofContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_getProof(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_getProofContext* SMTLIBv2Parser::cmd_getProof() {
  Cmd_getProofContext *_localctx = _tracker.createInstance<Cmd_getProofContext>(_ctx, getState());
  enterRule(_localctx, 124, SMTLIBv2Parser::RuleCmd_getProof);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(679);
    match(SMTLIBv2Parser::CMD_GetProof);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_getUnsatAssumptionsContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_getUnsatAssumptionsContext::Cmd_getUnsatAssumptionsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_getUnsatAssumptionsContext::CMD_GetUnsatAssumptions() {
  return getToken(SMTLIBv2Parser::CMD_GetUnsatAssumptions, 0);
}


size_t SMTLIBv2Parser::Cmd_getUnsatAssumptionsContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_getUnsatAssumptions;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_getUnsatAssumptionsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_getUnsatAssumptions(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_getUnsatAssumptionsContext* SMTLIBv2Parser::cmd_getUnsatAssumptions() {
  Cmd_getUnsatAssumptionsContext *_localctx = _tracker.createInstance<Cmd_getUnsatAssumptionsContext>(_ctx, getState());
  enterRule(_localctx, 126, SMTLIBv2Parser::RuleCmd_getUnsatAssumptions);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(681);
    match(SMTLIBv2Parser::CMD_GetUnsatAssumptions);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_getUnsatCoreContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_getUnsatCoreContext::Cmd_getUnsatCoreContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_getUnsatCoreContext::CMD_GetUnsatCore() {
  return getToken(SMTLIBv2Parser::CMD_GetUnsatCore, 0);
}


size_t SMTLIBv2Parser::Cmd_getUnsatCoreContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_getUnsatCore;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_getUnsatCoreContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_getUnsatCore(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_getUnsatCoreContext* SMTLIBv2Parser::cmd_getUnsatCore() {
  Cmd_getUnsatCoreContext *_localctx = _tracker.createInstance<Cmd_getUnsatCoreContext>(_ctx, getState());
  enterRule(_localctx, 128, SMTLIBv2Parser::RuleCmd_getUnsatCore);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(683);
    match(SMTLIBv2Parser::CMD_GetUnsatCore);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_getValueContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_getValueContext::Cmd_getValueContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_getValueContext::CMD_GetValue() {
  return getToken(SMTLIBv2Parser::CMD_GetValue, 0);
}


size_t SMTLIBv2Parser::Cmd_getValueContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_getValue;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_getValueContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_getValue(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_getValueContext* SMTLIBv2Parser::cmd_getValue() {
  Cmd_getValueContext *_localctx = _tracker.createInstance<Cmd_getValueContext>(_ctx, getState());
  enterRule(_localctx, 130, SMTLIBv2Parser::RuleCmd_getValue);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(685);
    match(SMTLIBv2Parser::CMD_GetValue);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_popContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_popContext::Cmd_popContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_popContext::CMD_Pop() {
  return getToken(SMTLIBv2Parser::CMD_Pop, 0);
}


size_t SMTLIBv2Parser::Cmd_popContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_pop;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_popContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_pop(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_popContext* SMTLIBv2Parser::cmd_pop() {
  Cmd_popContext *_localctx = _tracker.createInstance<Cmd_popContext>(_ctx, getState());
  enterRule(_localctx, 132, SMTLIBv2Parser::RuleCmd_pop);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(687);
    match(SMTLIBv2Parser::CMD_Pop);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_pushContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_pushContext::Cmd_pushContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_pushContext::CMD_Push() {
  return getToken(SMTLIBv2Parser::CMD_Push, 0);
}


size_t SMTLIBv2Parser::Cmd_pushContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_push;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_pushContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_push(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_pushContext* SMTLIBv2Parser::cmd_push() {
  Cmd_pushContext *_localctx = _tracker.createInstance<Cmd_pushContext>(_ctx, getState());
  enterRule(_localctx, 134, SMTLIBv2Parser::RuleCmd_push);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(689);
    match(SMTLIBv2Parser::CMD_Push);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_resetContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_resetContext::Cmd_resetContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_resetContext::CMD_Reset() {
  return getToken(SMTLIBv2Parser::CMD_Reset, 0);
}


size_t SMTLIBv2Parser::Cmd_resetContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_reset;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_resetContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_reset(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_resetContext* SMTLIBv2Parser::cmd_reset() {
  Cmd_resetContext *_localctx = _tracker.createInstance<Cmd_resetContext>(_ctx, getState());
  enterRule(_localctx, 136, SMTLIBv2Parser::RuleCmd_reset);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(691);
    match(SMTLIBv2Parser::CMD_Reset);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_resetAssertionsContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_resetAssertionsContext::Cmd_resetAssertionsContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_resetAssertionsContext::CMD_ResetAssertions() {
  return getToken(SMTLIBv2Parser::CMD_ResetAssertions, 0);
}


size_t SMTLIBv2Parser::Cmd_resetAssertionsContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_resetAssertions;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_resetAssertionsContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_resetAssertions(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_resetAssertionsContext* SMTLIBv2Parser::cmd_resetAssertions() {
  Cmd_resetAssertionsContext *_localctx = _tracker.createInstance<Cmd_resetAssertionsContext>(_ctx, getState());
  enterRule(_localctx, 138, SMTLIBv2Parser::RuleCmd_resetAssertions);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(693);
    match(SMTLIBv2Parser::CMD_ResetAssertions);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_setInfoContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_setInfoContext::Cmd_setInfoContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_setInfoContext::CMD_SetInfo() {
  return getToken(SMTLIBv2Parser::CMD_SetInfo, 0);
}


size_t SMTLIBv2Parser::Cmd_setInfoContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_setInfo;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_setInfoContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_setInfo(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_setInfoContext* SMTLIBv2Parser::cmd_setInfo() {
  Cmd_setInfoContext *_localctx = _tracker.createInstance<Cmd_setInfoContext>(_ctx, getState());
  enterRule(_localctx, 140, SMTLIBv2Parser::RuleCmd_setInfo);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(695);
    match(SMTLIBv2Parser::CMD_SetInfo);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_setLogicContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_setLogicContext::Cmd_setLogicContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_setLogicContext::CMD_SetLogic() {
  return getToken(SMTLIBv2Parser::CMD_SetLogic, 0);
}


size_t SMTLIBv2Parser::Cmd_setLogicContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_setLogic;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_setLogicContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_setLogic(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_setLogicContext* SMTLIBv2Parser::cmd_setLogic() {
  Cmd_setLogicContext *_localctx = _tracker.createInstance<Cmd_setLogicContext>(_ctx, getState());
  enterRule(_localctx, 142, SMTLIBv2Parser::RuleCmd_setLogic);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(697);
    match(SMTLIBv2Parser::CMD_SetLogic);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Cmd_setOptionContext ------------------------------------------------------------------

SMTLIBv2Parser::Cmd_setOptionContext::Cmd_setOptionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Cmd_setOptionContext::CMD_SetOption() {
  return getToken(SMTLIBv2Parser::CMD_SetOption, 0);
}


size_t SMTLIBv2Parser::Cmd_setOptionContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCmd_setOption;
}

antlrcpp::Any SMTLIBv2Parser::Cmd_setOptionContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCmd_setOption(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Cmd_setOptionContext* SMTLIBv2Parser::cmd_setOption() {
  Cmd_setOptionContext *_localctx = _tracker.createInstance<Cmd_setOptionContext>(_ctx, getState());
  enterRule(_localctx, 144, SMTLIBv2Parser::RuleCmd_setOption);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(699);
    match(SMTLIBv2Parser::CMD_SetOption);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- CommandContext ------------------------------------------------------------------

SMTLIBv2Parser::CommandContext::CommandContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::CommandContext::ParOpen() {
  return getTokens(SMTLIBv2Parser::ParOpen);
}

tree::TerminalNode* SMTLIBv2Parser::CommandContext::ParOpen(size_t i) {
  return getToken(SMTLIBv2Parser::ParOpen, i);
}

SMTLIBv2Parser::Cmd_assertContext* SMTLIBv2Parser::CommandContext::cmd_assert() {
  return getRuleContext<SMTLIBv2Parser::Cmd_assertContext>(0);
}

std::vector<SMTLIBv2Parser::TermContext *> SMTLIBv2Parser::CommandContext::term() {
  return getRuleContexts<SMTLIBv2Parser::TermContext>();
}

SMTLIBv2Parser::TermContext* SMTLIBv2Parser::CommandContext::term(size_t i) {
  return getRuleContext<SMTLIBv2Parser::TermContext>(i);
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::CommandContext::ParClose() {
  return getTokens(SMTLIBv2Parser::ParClose);
}

tree::TerminalNode* SMTLIBv2Parser::CommandContext::ParClose(size_t i) {
  return getToken(SMTLIBv2Parser::ParClose, i);
}

SMTLIBv2Parser::Cmd_checkSatContext* SMTLIBv2Parser::CommandContext::cmd_checkSat() {
  return getRuleContext<SMTLIBv2Parser::Cmd_checkSatContext>(0);
}

SMTLIBv2Parser::Cmd_checkSatAssumingContext* SMTLIBv2Parser::CommandContext::cmd_checkSatAssuming() {
  return getRuleContext<SMTLIBv2Parser::Cmd_checkSatAssumingContext>(0);
}

SMTLIBv2Parser::Cmd_declareConstContext* SMTLIBv2Parser::CommandContext::cmd_declareConst() {
  return getRuleContext<SMTLIBv2Parser::Cmd_declareConstContext>(0);
}

std::vector<SMTLIBv2Parser::SymbolContext *> SMTLIBv2Parser::CommandContext::symbol() {
  return getRuleContexts<SMTLIBv2Parser::SymbolContext>();
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::CommandContext::symbol(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(i);
}

std::vector<SMTLIBv2Parser::SortContext *> SMTLIBv2Parser::CommandContext::sort() {
  return getRuleContexts<SMTLIBv2Parser::SortContext>();
}

SMTLIBv2Parser::SortContext* SMTLIBv2Parser::CommandContext::sort(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SortContext>(i);
}

SMTLIBv2Parser::Cmd_declareDatatypeContext* SMTLIBv2Parser::CommandContext::cmd_declareDatatype() {
  return getRuleContext<SMTLIBv2Parser::Cmd_declareDatatypeContext>(0);
}

std::vector<SMTLIBv2Parser::Datatype_decContext *> SMTLIBv2Parser::CommandContext::datatype_dec() {
  return getRuleContexts<SMTLIBv2Parser::Datatype_decContext>();
}

SMTLIBv2Parser::Datatype_decContext* SMTLIBv2Parser::CommandContext::datatype_dec(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Datatype_decContext>(i);
}

SMTLIBv2Parser::Cmd_declareDatatypesContext* SMTLIBv2Parser::CommandContext::cmd_declareDatatypes() {
  return getRuleContext<SMTLIBv2Parser::Cmd_declareDatatypesContext>(0);
}

std::vector<SMTLIBv2Parser::Sort_decContext *> SMTLIBv2Parser::CommandContext::sort_dec() {
  return getRuleContexts<SMTLIBv2Parser::Sort_decContext>();
}

SMTLIBv2Parser::Sort_decContext* SMTLIBv2Parser::CommandContext::sort_dec(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Sort_decContext>(i);
}

SMTLIBv2Parser::Cmd_declareFunContext* SMTLIBv2Parser::CommandContext::cmd_declareFun() {
  return getRuleContext<SMTLIBv2Parser::Cmd_declareFunContext>(0);
}

SMTLIBv2Parser::Cmd_declareSortContext* SMTLIBv2Parser::CommandContext::cmd_declareSort() {
  return getRuleContext<SMTLIBv2Parser::Cmd_declareSortContext>(0);
}

SMTLIBv2Parser::NumeralContext* SMTLIBv2Parser::CommandContext::numeral() {
  return getRuleContext<SMTLIBv2Parser::NumeralContext>(0);
}

SMTLIBv2Parser::Cmd_defineFunContext* SMTLIBv2Parser::CommandContext::cmd_defineFun() {
  return getRuleContext<SMTLIBv2Parser::Cmd_defineFunContext>(0);
}

SMTLIBv2Parser::Function_defContext* SMTLIBv2Parser::CommandContext::function_def() {
  return getRuleContext<SMTLIBv2Parser::Function_defContext>(0);
}

SMTLIBv2Parser::Cmd_defineFunRecContext* SMTLIBv2Parser::CommandContext::cmd_defineFunRec() {
  return getRuleContext<SMTLIBv2Parser::Cmd_defineFunRecContext>(0);
}

SMTLIBv2Parser::Cmd_defineFunsRecContext* SMTLIBv2Parser::CommandContext::cmd_defineFunsRec() {
  return getRuleContext<SMTLIBv2Parser::Cmd_defineFunsRecContext>(0);
}

std::vector<SMTLIBv2Parser::Function_decContext *> SMTLIBv2Parser::CommandContext::function_dec() {
  return getRuleContexts<SMTLIBv2Parser::Function_decContext>();
}

SMTLIBv2Parser::Function_decContext* SMTLIBv2Parser::CommandContext::function_dec(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Function_decContext>(i);
}

SMTLIBv2Parser::Cmd_defineSortContext* SMTLIBv2Parser::CommandContext::cmd_defineSort() {
  return getRuleContext<SMTLIBv2Parser::Cmd_defineSortContext>(0);
}

SMTLIBv2Parser::Cmd_echoContext* SMTLIBv2Parser::CommandContext::cmd_echo() {
  return getRuleContext<SMTLIBv2Parser::Cmd_echoContext>(0);
}

SMTLIBv2Parser::StringContext* SMTLIBv2Parser::CommandContext::string() {
  return getRuleContext<SMTLIBv2Parser::StringContext>(0);
}

SMTLIBv2Parser::Cmd_exitContext* SMTLIBv2Parser::CommandContext::cmd_exit() {
  return getRuleContext<SMTLIBv2Parser::Cmd_exitContext>(0);
}

SMTLIBv2Parser::Cmd_getAssertionsContext* SMTLIBv2Parser::CommandContext::cmd_getAssertions() {
  return getRuleContext<SMTLIBv2Parser::Cmd_getAssertionsContext>(0);
}

SMTLIBv2Parser::Cmd_getAssignmentContext* SMTLIBv2Parser::CommandContext::cmd_getAssignment() {
  return getRuleContext<SMTLIBv2Parser::Cmd_getAssignmentContext>(0);
}

SMTLIBv2Parser::Cmd_getInfoContext* SMTLIBv2Parser::CommandContext::cmd_getInfo() {
  return getRuleContext<SMTLIBv2Parser::Cmd_getInfoContext>(0);
}

SMTLIBv2Parser::Info_flagContext* SMTLIBv2Parser::CommandContext::info_flag() {
  return getRuleContext<SMTLIBv2Parser::Info_flagContext>(0);
}

SMTLIBv2Parser::Cmd_getModelContext* SMTLIBv2Parser::CommandContext::cmd_getModel() {
  return getRuleContext<SMTLIBv2Parser::Cmd_getModelContext>(0);
}

SMTLIBv2Parser::Cmd_getOptionContext* SMTLIBv2Parser::CommandContext::cmd_getOption() {
  return getRuleContext<SMTLIBv2Parser::Cmd_getOptionContext>(0);
}

SMTLIBv2Parser::KeywordContext* SMTLIBv2Parser::CommandContext::keyword() {
  return getRuleContext<SMTLIBv2Parser::KeywordContext>(0);
}

SMTLIBv2Parser::Cmd_getProofContext* SMTLIBv2Parser::CommandContext::cmd_getProof() {
  return getRuleContext<SMTLIBv2Parser::Cmd_getProofContext>(0);
}

SMTLIBv2Parser::Cmd_getUnsatAssumptionsContext* SMTLIBv2Parser::CommandContext::cmd_getUnsatAssumptions() {
  return getRuleContext<SMTLIBv2Parser::Cmd_getUnsatAssumptionsContext>(0);
}

SMTLIBv2Parser::Cmd_getUnsatCoreContext* SMTLIBv2Parser::CommandContext::cmd_getUnsatCore() {
  return getRuleContext<SMTLIBv2Parser::Cmd_getUnsatCoreContext>(0);
}

SMTLIBv2Parser::Cmd_getValueContext* SMTLIBv2Parser::CommandContext::cmd_getValue() {
  return getRuleContext<SMTLIBv2Parser::Cmd_getValueContext>(0);
}

SMTLIBv2Parser::Cmd_popContext* SMTLIBv2Parser::CommandContext::cmd_pop() {
  return getRuleContext<SMTLIBv2Parser::Cmd_popContext>(0);
}

SMTLIBv2Parser::Cmd_pushContext* SMTLIBv2Parser::CommandContext::cmd_push() {
  return getRuleContext<SMTLIBv2Parser::Cmd_pushContext>(0);
}

SMTLIBv2Parser::Cmd_resetContext* SMTLIBv2Parser::CommandContext::cmd_reset() {
  return getRuleContext<SMTLIBv2Parser::Cmd_resetContext>(0);
}

SMTLIBv2Parser::Cmd_resetAssertionsContext* SMTLIBv2Parser::CommandContext::cmd_resetAssertions() {
  return getRuleContext<SMTLIBv2Parser::Cmd_resetAssertionsContext>(0);
}

SMTLIBv2Parser::Cmd_setInfoContext* SMTLIBv2Parser::CommandContext::cmd_setInfo() {
  return getRuleContext<SMTLIBv2Parser::Cmd_setInfoContext>(0);
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::CommandContext::attribute() {
  return getRuleContext<SMTLIBv2Parser::AttributeContext>(0);
}

SMTLIBv2Parser::Cmd_setLogicContext* SMTLIBv2Parser::CommandContext::cmd_setLogic() {
  return getRuleContext<SMTLIBv2Parser::Cmd_setLogicContext>(0);
}

SMTLIBv2Parser::Cmd_setOptionContext* SMTLIBv2Parser::CommandContext::cmd_setOption() {
  return getRuleContext<SMTLIBv2Parser::Cmd_setOptionContext>(0);
}

SMTLIBv2Parser::OptionContext* SMTLIBv2Parser::CommandContext::option() {
  return getRuleContext<SMTLIBv2Parser::OptionContext>(0);
}


size_t SMTLIBv2Parser::CommandContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCommand;
}

antlrcpp::Any SMTLIBv2Parser::CommandContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCommand(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::CommandContext* SMTLIBv2Parser::command() {
  CommandContext *_localctx = _tracker.createInstance<CommandContext>(_ctx, getState());
  enterRule(_localctx, 146, SMTLIBv2Parser::RuleCommand);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(893);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 57, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(701);
      match(SMTLIBv2Parser::ParOpen);
      setState(702);
      cmd_assert();
      setState(703);
      term();
      setState(704);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(706);
      match(SMTLIBv2Parser::ParOpen);
      setState(707);
      cmd_checkSat();
      setState(708);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(710);
      match(SMTLIBv2Parser::ParOpen);
      setState(711);
      cmd_checkSatAssuming();
      setState(712);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(714);
      match(SMTLIBv2Parser::ParOpen);
      setState(715);
      cmd_declareConst();
      setState(716);
      symbol();
      setState(717);
      sort();
      setState(718);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(720);
      match(SMTLIBv2Parser::ParOpen);
      setState(721);
      cmd_declareDatatype();
      setState(722);
      symbol();
      setState(723);
      datatype_dec();
      setState(724);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(726);
      match(SMTLIBv2Parser::ParOpen);
      setState(727);
      cmd_declareDatatypes();
      setState(728);
      match(SMTLIBv2Parser::ParOpen);
      setState(730); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(729);
        sort_dec();
        setState(732); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(734);
      match(SMTLIBv2Parser::ParClose);
      setState(735);
      match(SMTLIBv2Parser::ParOpen);
      setState(737); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(736);
        datatype_dec();
        setState(739); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(741);
      match(SMTLIBv2Parser::ParClose);
      setState(742);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(744);
      match(SMTLIBv2Parser::ParOpen);
      setState(745);
      cmd_declareFun();
      setState(746);
      symbol();
      setState(747);
      match(SMTLIBv2Parser::ParOpen);
      setState(751);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
        | (1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol) {
        setState(748);
        sort();
        setState(753);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(754);
      match(SMTLIBv2Parser::ParClose);
      setState(755);
      sort();
      setState(756);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(758);
      match(SMTLIBv2Parser::ParOpen);
      setState(759);
      cmd_declareSort();
      setState(760);
      symbol();
      setState(761);
      numeral();
      setState(762);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 9: {
      enterOuterAlt(_localctx, 9);
      setState(764);
      match(SMTLIBv2Parser::ParOpen);
      setState(765);
      cmd_defineFun();
      setState(766);
      function_def();
      setState(767);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 10: {
      enterOuterAlt(_localctx, 10);
      setState(769);
      match(SMTLIBv2Parser::ParOpen);
      setState(770);
      cmd_defineFunRec();
      setState(771);
      function_def();
      setState(772);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 11: {
      enterOuterAlt(_localctx, 11);
      setState(774);
      match(SMTLIBv2Parser::ParOpen);
      setState(775);
      cmd_defineFunsRec();
      setState(776);
      match(SMTLIBv2Parser::ParOpen);
      setState(778); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(777);
        function_dec();
        setState(780); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(782);
      match(SMTLIBv2Parser::ParClose);
      setState(783);
      match(SMTLIBv2Parser::ParOpen);
      setState(785); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(784);
        term();
        setState(787); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
        | (1ULL << SMTLIBv2Parser::String)
        | (1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || ((((_la - 66) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 66)) & ((1ULL << (SMTLIBv2Parser::Numeral - 66))
        | (1ULL << (SMTLIBv2Parser::Binary - 66))
        | (1ULL << (SMTLIBv2Parser::HexDecimal - 66))
        | (1ULL << (SMTLIBv2Parser::Decimal - 66))
        | (1ULL << (SMTLIBv2Parser::UndefinedSymbol - 66)))) != 0));
      setState(789);
      match(SMTLIBv2Parser::ParClose);
      setState(790);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 12: {
      enterOuterAlt(_localctx, 12);
      setState(792);
      match(SMTLIBv2Parser::ParOpen);
      setState(793);
      cmd_defineSort();
      setState(794);
      symbol();
      setState(795);
      match(SMTLIBv2Parser::ParOpen);
      setState(799);
      _errHandler->sync(this);
      _la = _input->LA(1);
      while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol) {
        setState(796);
        symbol();
        setState(801);
        _errHandler->sync(this);
        _la = _input->LA(1);
      }
      setState(802);
      match(SMTLIBv2Parser::ParClose);
      setState(803);
      sort();
      setState(804);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 13: {
      enterOuterAlt(_localctx, 13);
      setState(806);
      match(SMTLIBv2Parser::ParOpen);
      setState(807);
      cmd_echo();
      setState(808);
      string();
      setState(809);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 14: {
      enterOuterAlt(_localctx, 14);
      setState(811);
      match(SMTLIBv2Parser::ParOpen);
      setState(812);
      cmd_exit();
      setState(813);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 15: {
      enterOuterAlt(_localctx, 15);
      setState(815);
      match(SMTLIBv2Parser::ParOpen);
      setState(816);
      cmd_getAssertions();
      setState(817);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 16: {
      enterOuterAlt(_localctx, 16);
      setState(819);
      match(SMTLIBv2Parser::ParOpen);
      setState(820);
      cmd_getAssignment();
      setState(821);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 17: {
      enterOuterAlt(_localctx, 17);
      setState(823);
      match(SMTLIBv2Parser::ParOpen);
      setState(824);
      cmd_getInfo();
      setState(825);
      info_flag();
      setState(826);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 18: {
      enterOuterAlt(_localctx, 18);
      setState(828);
      match(SMTLIBv2Parser::ParOpen);
      setState(829);
      cmd_getModel();
      setState(830);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 19: {
      enterOuterAlt(_localctx, 19);
      setState(832);
      match(SMTLIBv2Parser::ParOpen);
      setState(833);
      cmd_getOption();
      setState(834);
      keyword();
      setState(835);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 20: {
      enterOuterAlt(_localctx, 20);
      setState(837);
      match(SMTLIBv2Parser::ParOpen);
      setState(838);
      cmd_getProof();
      setState(839);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 21: {
      enterOuterAlt(_localctx, 21);
      setState(841);
      match(SMTLIBv2Parser::ParOpen);
      setState(842);
      cmd_getUnsatAssumptions();
      setState(843);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 22: {
      enterOuterAlt(_localctx, 22);
      setState(845);
      match(SMTLIBv2Parser::ParOpen);
      setState(846);
      cmd_getUnsatCore();
      setState(847);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 23: {
      enterOuterAlt(_localctx, 23);
      setState(849);
      match(SMTLIBv2Parser::ParOpen);
      setState(850);
      cmd_getValue();
      setState(851);
      match(SMTLIBv2Parser::ParOpen);
      setState(853); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(852);
        term();
        setState(855); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
        | (1ULL << SMTLIBv2Parser::String)
        | (1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || ((((_la - 66) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 66)) & ((1ULL << (SMTLIBv2Parser::Numeral - 66))
        | (1ULL << (SMTLIBv2Parser::Binary - 66))
        | (1ULL << (SMTLIBv2Parser::HexDecimal - 66))
        | (1ULL << (SMTLIBv2Parser::Decimal - 66))
        | (1ULL << (SMTLIBv2Parser::UndefinedSymbol - 66)))) != 0));
      setState(857);
      match(SMTLIBv2Parser::ParClose);
      setState(858);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 24: {
      enterOuterAlt(_localctx, 24);
      setState(860);
      match(SMTLIBv2Parser::ParOpen);
      setState(861);
      cmd_pop();
      setState(862);
      numeral();
      setState(863);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 25: {
      enterOuterAlt(_localctx, 25);
      setState(865);
      match(SMTLIBv2Parser::ParOpen);
      setState(866);
      cmd_push();
      setState(867);
      numeral();
      setState(868);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 26: {
      enterOuterAlt(_localctx, 26);
      setState(870);
      match(SMTLIBv2Parser::ParOpen);
      setState(871);
      cmd_reset();
      setState(872);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 27: {
      enterOuterAlt(_localctx, 27);
      setState(874);
      match(SMTLIBv2Parser::ParOpen);
      setState(875);
      cmd_resetAssertions();
      setState(876);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 28: {
      enterOuterAlt(_localctx, 28);
      setState(878);
      match(SMTLIBv2Parser::ParOpen);
      setState(879);
      cmd_setInfo();
      setState(880);
      attribute();
      setState(881);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 29: {
      enterOuterAlt(_localctx, 29);
      setState(883);
      match(SMTLIBv2Parser::ParOpen);
      setState(884);
      cmd_setLogic();
      setState(885);
      symbol();
      setState(886);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 30: {
      enterOuterAlt(_localctx, 30);
      setState(888);
      match(SMTLIBv2Parser::ParOpen);
      setState(889);
      cmd_setOption();
      setState(890);
      option();
      setState(891);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- B_valueContext ------------------------------------------------------------------

SMTLIBv2Parser::B_valueContext::B_valueContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::B_valueContext::PS_True() {
  return getToken(SMTLIBv2Parser::PS_True, 0);
}

tree::TerminalNode* SMTLIBv2Parser::B_valueContext::PS_False() {
  return getToken(SMTLIBv2Parser::PS_False, 0);
}


size_t SMTLIBv2Parser::B_valueContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleB_value;
}

antlrcpp::Any SMTLIBv2Parser::B_valueContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitB_value(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::B_valueContext* SMTLIBv2Parser::b_value() {
  B_valueContext *_localctx = _tracker.createInstance<B_valueContext>(_ctx, getState());
  enterRule(_localctx, 148, SMTLIBv2Parser::RuleB_value);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(895);
    _la = _input->LA(1);
    if (!(_la == SMTLIBv2Parser::PS_False

    || _la == SMTLIBv2Parser::PS_True)) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- OptionContext ------------------------------------------------------------------

SMTLIBv2Parser::OptionContext::OptionContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_DiagnosticOutputChannel() {
  return getToken(SMTLIBv2Parser::PK_DiagnosticOutputChannel, 0);
}

SMTLIBv2Parser::StringContext* SMTLIBv2Parser::OptionContext::string() {
  return getRuleContext<SMTLIBv2Parser::StringContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_GlobalDeclarations() {
  return getToken(SMTLIBv2Parser::PK_GlobalDeclarations, 0);
}

SMTLIBv2Parser::B_valueContext* SMTLIBv2Parser::OptionContext::b_value() {
  return getRuleContext<SMTLIBv2Parser::B_valueContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_InteractiveMode() {
  return getToken(SMTLIBv2Parser::PK_InteractiveMode, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_PrintSuccess() {
  return getToken(SMTLIBv2Parser::PK_PrintSuccess, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_ProduceAssertions() {
  return getToken(SMTLIBv2Parser::PK_ProduceAssertions, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_ProduceAssignments() {
  return getToken(SMTLIBv2Parser::PK_ProduceAssignments, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_ProduceModels() {
  return getToken(SMTLIBv2Parser::PK_ProduceModels, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_ProduceProofs() {
  return getToken(SMTLIBv2Parser::PK_ProduceProofs, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_ProduceUnsatAssumptions() {
  return getToken(SMTLIBv2Parser::PK_ProduceUnsatAssumptions, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_ProduceUnsatCores() {
  return getToken(SMTLIBv2Parser::PK_ProduceUnsatCores, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_RandomSeed() {
  return getToken(SMTLIBv2Parser::PK_RandomSeed, 0);
}

SMTLIBv2Parser::NumeralContext* SMTLIBv2Parser::OptionContext::numeral() {
  return getRuleContext<SMTLIBv2Parser::NumeralContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_RegularOutputChannel() {
  return getToken(SMTLIBv2Parser::PK_RegularOutputChannel, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_ReproducibleResourceLimit() {
  return getToken(SMTLIBv2Parser::PK_ReproducibleResourceLimit, 0);
}

tree::TerminalNode* SMTLIBv2Parser::OptionContext::PK_Verbosity() {
  return getToken(SMTLIBv2Parser::PK_Verbosity, 0);
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::OptionContext::attribute() {
  return getRuleContext<SMTLIBv2Parser::AttributeContext>(0);
}


size_t SMTLIBv2Parser::OptionContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleOption;
}

antlrcpp::Any SMTLIBv2Parser::OptionContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitOption(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::OptionContext* SMTLIBv2Parser::option() {
  OptionContext *_localctx = _tracker.createInstance<OptionContext>(_ctx, getState());
  enterRule(_localctx, 150, SMTLIBv2Parser::RuleOption);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(926);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 58, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(897);
      match(SMTLIBv2Parser::PK_DiagnosticOutputChannel);
      setState(898);
      string();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(899);
      match(SMTLIBv2Parser::PK_GlobalDeclarations);
      setState(900);
      b_value();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(901);
      match(SMTLIBv2Parser::PK_InteractiveMode);
      setState(902);
      b_value();
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(903);
      match(SMTLIBv2Parser::PK_PrintSuccess);
      setState(904);
      b_value();
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(905);
      match(SMTLIBv2Parser::PK_ProduceAssertions);
      setState(906);
      b_value();
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(907);
      match(SMTLIBv2Parser::PK_ProduceAssignments);
      setState(908);
      b_value();
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(909);
      match(SMTLIBv2Parser::PK_ProduceModels);
      setState(910);
      b_value();
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(911);
      match(SMTLIBv2Parser::PK_ProduceProofs);
      setState(912);
      b_value();
      break;
    }

    case 9: {
      enterOuterAlt(_localctx, 9);
      setState(913);
      match(SMTLIBv2Parser::PK_ProduceUnsatAssumptions);
      setState(914);
      b_value();
      break;
    }

    case 10: {
      enterOuterAlt(_localctx, 10);
      setState(915);
      match(SMTLIBv2Parser::PK_ProduceUnsatCores);
      setState(916);
      b_value();
      break;
    }

    case 11: {
      enterOuterAlt(_localctx, 11);
      setState(917);
      match(SMTLIBv2Parser::PK_RandomSeed);
      setState(918);
      numeral();
      break;
    }

    case 12: {
      enterOuterAlt(_localctx, 12);
      setState(919);
      match(SMTLIBv2Parser::PK_RegularOutputChannel);
      setState(920);
      string();
      break;
    }

    case 13: {
      enterOuterAlt(_localctx, 13);
      setState(921);
      match(SMTLIBv2Parser::PK_ReproducibleResourceLimit);
      setState(922);
      numeral();
      break;
    }

    case 14: {
      enterOuterAlt(_localctx, 14);
      setState(923);
      match(SMTLIBv2Parser::PK_Verbosity);
      setState(924);
      numeral();
      break;
    }

    case 15: {
      enterOuterAlt(_localctx, 15);
      setState(925);
      attribute();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Info_flagContext ------------------------------------------------------------------

SMTLIBv2Parser::Info_flagContext::Info_flagContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Info_flagContext::PK_AllStatistics() {
  return getToken(SMTLIBv2Parser::PK_AllStatistics, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_flagContext::PK_AssertionStackLevels() {
  return getToken(SMTLIBv2Parser::PK_AssertionStackLevels, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_flagContext::PK_Authors() {
  return getToken(SMTLIBv2Parser::PK_Authors, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_flagContext::PK_ErrorBehaviour() {
  return getToken(SMTLIBv2Parser::PK_ErrorBehaviour, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_flagContext::PK_Name() {
  return getToken(SMTLIBv2Parser::PK_Name, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_flagContext::PK_ReasonUnknown() {
  return getToken(SMTLIBv2Parser::PK_ReasonUnknown, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_flagContext::PK_Version() {
  return getToken(SMTLIBv2Parser::PK_Version, 0);
}

SMTLIBv2Parser::KeywordContext* SMTLIBv2Parser::Info_flagContext::keyword() {
  return getRuleContext<SMTLIBv2Parser::KeywordContext>(0);
}


size_t SMTLIBv2Parser::Info_flagContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleInfo_flag;
}

antlrcpp::Any SMTLIBv2Parser::Info_flagContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitInfo_flag(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Info_flagContext* SMTLIBv2Parser::info_flag() {
  Info_flagContext *_localctx = _tracker.createInstance<Info_flagContext>(_ctx, getState());
  enterRule(_localctx, 152, SMTLIBv2Parser::RuleInfo_flag);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(936);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 59, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(928);
      match(SMTLIBv2Parser::PK_AllStatistics);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(929);
      match(SMTLIBv2Parser::PK_AssertionStackLevels);
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(930);
      match(SMTLIBv2Parser::PK_Authors);
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(931);
      match(SMTLIBv2Parser::PK_ErrorBehaviour);
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(932);
      match(SMTLIBv2Parser::PK_Name);
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(933);
      match(SMTLIBv2Parser::PK_ReasonUnknown);
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(934);
      match(SMTLIBv2Parser::PK_Version);
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(935);
      keyword();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Error_behaviourContext ------------------------------------------------------------------

SMTLIBv2Parser::Error_behaviourContext::Error_behaviourContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Error_behaviourContext::PS_ImmediateExit() {
  return getToken(SMTLIBv2Parser::PS_ImmediateExit, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Error_behaviourContext::PS_ContinuedExecution() {
  return getToken(SMTLIBv2Parser::PS_ContinuedExecution, 0);
}


size_t SMTLIBv2Parser::Error_behaviourContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleError_behaviour;
}

antlrcpp::Any SMTLIBv2Parser::Error_behaviourContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitError_behaviour(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Error_behaviourContext* SMTLIBv2Parser::error_behaviour() {
  Error_behaviourContext *_localctx = _tracker.createInstance<Error_behaviourContext>(_ctx, getState());
  enterRule(_localctx, 154, SMTLIBv2Parser::RuleError_behaviour);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(938);
    _la = _input->LA(1);
    if (!(_la == SMTLIBv2Parser::PS_ContinuedExecution

    || _la == SMTLIBv2Parser::PS_ImmediateExit)) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Reason_unknownContext ------------------------------------------------------------------

SMTLIBv2Parser::Reason_unknownContext::Reason_unknownContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Reason_unknownContext::PS_Memout() {
  return getToken(SMTLIBv2Parser::PS_Memout, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Reason_unknownContext::PS_Incomplete() {
  return getToken(SMTLIBv2Parser::PS_Incomplete, 0);
}

SMTLIBv2Parser::S_exprContext* SMTLIBv2Parser::Reason_unknownContext::s_expr() {
  return getRuleContext<SMTLIBv2Parser::S_exprContext>(0);
}


size_t SMTLIBv2Parser::Reason_unknownContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleReason_unknown;
}

antlrcpp::Any SMTLIBv2Parser::Reason_unknownContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitReason_unknown(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Reason_unknownContext* SMTLIBv2Parser::reason_unknown() {
  Reason_unknownContext *_localctx = _tracker.createInstance<Reason_unknownContext>(_ctx, getState());
  enterRule(_localctx, 156, SMTLIBv2Parser::RuleReason_unknown);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(943);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 60, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(940);
      match(SMTLIBv2Parser::PS_Memout);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(941);
      match(SMTLIBv2Parser::PS_Incomplete);
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(942);
      s_expr();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Model_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Model_responseContext::Model_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::Model_responseContext::ParOpen() {
  return getTokens(SMTLIBv2Parser::ParOpen);
}

tree::TerminalNode* SMTLIBv2Parser::Model_responseContext::ParOpen(size_t i) {
  return getToken(SMTLIBv2Parser::ParOpen, i);
}

tree::TerminalNode* SMTLIBv2Parser::Model_responseContext::CMD_DefineFun() {
  return getToken(SMTLIBv2Parser::CMD_DefineFun, 0);
}

SMTLIBv2Parser::Function_defContext* SMTLIBv2Parser::Model_responseContext::function_def() {
  return getRuleContext<SMTLIBv2Parser::Function_defContext>(0);
}

std::vector<tree::TerminalNode *> SMTLIBv2Parser::Model_responseContext::ParClose() {
  return getTokens(SMTLIBv2Parser::ParClose);
}

tree::TerminalNode* SMTLIBv2Parser::Model_responseContext::ParClose(size_t i) {
  return getToken(SMTLIBv2Parser::ParClose, i);
}

tree::TerminalNode* SMTLIBv2Parser::Model_responseContext::CMD_DefineFunRec() {
  return getToken(SMTLIBv2Parser::CMD_DefineFunRec, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Model_responseContext::CMD_DefineFunsRec() {
  return getToken(SMTLIBv2Parser::CMD_DefineFunsRec, 0);
}

std::vector<SMTLIBv2Parser::Function_decContext *> SMTLIBv2Parser::Model_responseContext::function_dec() {
  return getRuleContexts<SMTLIBv2Parser::Function_decContext>();
}

SMTLIBv2Parser::Function_decContext* SMTLIBv2Parser::Model_responseContext::function_dec(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Function_decContext>(i);
}

std::vector<SMTLIBv2Parser::TermContext *> SMTLIBv2Parser::Model_responseContext::term() {
  return getRuleContexts<SMTLIBv2Parser::TermContext>();
}

SMTLIBv2Parser::TermContext* SMTLIBv2Parser::Model_responseContext::term(size_t i) {
  return getRuleContext<SMTLIBv2Parser::TermContext>(i);
}


size_t SMTLIBv2Parser::Model_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleModel_response;
}

antlrcpp::Any SMTLIBv2Parser::Model_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitModel_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Model_responseContext* SMTLIBv2Parser::model_response() {
  Model_responseContext *_localctx = _tracker.createInstance<Model_responseContext>(_ctx, getState());
  enterRule(_localctx, 158, SMTLIBv2Parser::RuleModel_response);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(973);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 63, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(945);
      match(SMTLIBv2Parser::ParOpen);
      setState(946);
      match(SMTLIBv2Parser::CMD_DefineFun);
      setState(947);
      function_def();
      setState(948);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(950);
      match(SMTLIBv2Parser::ParOpen);
      setState(951);
      match(SMTLIBv2Parser::CMD_DefineFunRec);
      setState(952);
      function_def();
      setState(953);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(955);
      match(SMTLIBv2Parser::ParOpen);
      setState(956);
      match(SMTLIBv2Parser::CMD_DefineFunsRec);
      setState(957);
      match(SMTLIBv2Parser::ParOpen);
      setState(959); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(958);
        function_dec();
        setState(961); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while (_la == SMTLIBv2Parser::ParOpen);
      setState(963);
      match(SMTLIBv2Parser::ParClose);
      setState(964);
      match(SMTLIBv2Parser::ParOpen);
      setState(966); 
      _errHandler->sync(this);
      _la = _input->LA(1);
      do {
        setState(965);
        term();
        setState(968); 
        _errHandler->sync(this);
        _la = _input->LA(1);
      } while ((((_la & ~ 0x3fULL) == 0) &&
        ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
        | (1ULL << SMTLIBv2Parser::String)
        | (1ULL << SMTLIBv2Parser::QuotedSymbol)
        | (1ULL << SMTLIBv2Parser::PS_Not)
        | (1ULL << SMTLIBv2Parser::PS_Bool)
        | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
        | (1ULL << SMTLIBv2Parser::PS_Error)
        | (1ULL << SMTLIBv2Parser::PS_False)
        | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
        | (1ULL << SMTLIBv2Parser::PS_Incomplete)
        | (1ULL << SMTLIBv2Parser::PS_Logic)
        | (1ULL << SMTLIBv2Parser::PS_Memout)
        | (1ULL << SMTLIBv2Parser::PS_Sat)
        | (1ULL << SMTLIBv2Parser::PS_Success)
        | (1ULL << SMTLIBv2Parser::PS_Theory)
        | (1ULL << SMTLIBv2Parser::PS_True)
        | (1ULL << SMTLIBv2Parser::PS_Unknown)
        | (1ULL << SMTLIBv2Parser::PS_Unsupported)
        | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || ((((_la - 66) & ~ 0x3fULL) == 0) &&
        ((1ULL << (_la - 66)) & ((1ULL << (SMTLIBv2Parser::Numeral - 66))
        | (1ULL << (SMTLIBv2Parser::Binary - 66))
        | (1ULL << (SMTLIBv2Parser::HexDecimal - 66))
        | (1ULL << (SMTLIBv2Parser::Decimal - 66))
        | (1ULL << (SMTLIBv2Parser::UndefinedSymbol - 66)))) != 0));
      setState(970);
      match(SMTLIBv2Parser::ParClose);
      setState(971);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Info_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Info_responseContext::Info_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Info_responseContext::PK_AssertionStackLevels() {
  return getToken(SMTLIBv2Parser::PK_AssertionStackLevels, 0);
}

SMTLIBv2Parser::NumeralContext* SMTLIBv2Parser::Info_responseContext::numeral() {
  return getRuleContext<SMTLIBv2Parser::NumeralContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_responseContext::PK_Authors() {
  return getToken(SMTLIBv2Parser::PK_Authors, 0);
}

SMTLIBv2Parser::StringContext* SMTLIBv2Parser::Info_responseContext::string() {
  return getRuleContext<SMTLIBv2Parser::StringContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_responseContext::PK_ErrorBehaviour() {
  return getToken(SMTLIBv2Parser::PK_ErrorBehaviour, 0);
}

SMTLIBv2Parser::Error_behaviourContext* SMTLIBv2Parser::Info_responseContext::error_behaviour() {
  return getRuleContext<SMTLIBv2Parser::Error_behaviourContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_responseContext::PK_Name() {
  return getToken(SMTLIBv2Parser::PK_Name, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_responseContext::PK_ReasonUnknown() {
  return getToken(SMTLIBv2Parser::PK_ReasonUnknown, 0);
}

SMTLIBv2Parser::Reason_unknownContext* SMTLIBv2Parser::Info_responseContext::reason_unknown() {
  return getRuleContext<SMTLIBv2Parser::Reason_unknownContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::Info_responseContext::PK_Version() {
  return getToken(SMTLIBv2Parser::PK_Version, 0);
}

SMTLIBv2Parser::AttributeContext* SMTLIBv2Parser::Info_responseContext::attribute() {
  return getRuleContext<SMTLIBv2Parser::AttributeContext>(0);
}


size_t SMTLIBv2Parser::Info_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleInfo_response;
}

antlrcpp::Any SMTLIBv2Parser::Info_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitInfo_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Info_responseContext* SMTLIBv2Parser::info_response() {
  Info_responseContext *_localctx = _tracker.createInstance<Info_responseContext>(_ctx, getState());
  enterRule(_localctx, 160, SMTLIBv2Parser::RuleInfo_response);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(988);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 64, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(975);
      match(SMTLIBv2Parser::PK_AssertionStackLevels);
      setState(976);
      numeral();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(977);
      match(SMTLIBv2Parser::PK_Authors);
      setState(978);
      string();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(979);
      match(SMTLIBv2Parser::PK_ErrorBehaviour);
      setState(980);
      error_behaviour();
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(981);
      match(SMTLIBv2Parser::PK_Name);
      setState(982);
      string();
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(983);
      match(SMTLIBv2Parser::PK_ReasonUnknown);
      setState(984);
      reason_unknown();
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(985);
      match(SMTLIBv2Parser::PK_Version);
      setState(986);
      string();
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(987);
      attribute();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Valuation_pairContext ------------------------------------------------------------------

SMTLIBv2Parser::Valuation_pairContext::Valuation_pairContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Valuation_pairContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

std::vector<SMTLIBv2Parser::TermContext *> SMTLIBv2Parser::Valuation_pairContext::term() {
  return getRuleContexts<SMTLIBv2Parser::TermContext>();
}

SMTLIBv2Parser::TermContext* SMTLIBv2Parser::Valuation_pairContext::term(size_t i) {
  return getRuleContext<SMTLIBv2Parser::TermContext>(i);
}

tree::TerminalNode* SMTLIBv2Parser::Valuation_pairContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::Valuation_pairContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleValuation_pair;
}

antlrcpp::Any SMTLIBv2Parser::Valuation_pairContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitValuation_pair(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Valuation_pairContext* SMTLIBv2Parser::valuation_pair() {
  Valuation_pairContext *_localctx = _tracker.createInstance<Valuation_pairContext>(_ctx, getState());
  enterRule(_localctx, 162, SMTLIBv2Parser::RuleValuation_pair);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(990);
    match(SMTLIBv2Parser::ParOpen);
    setState(991);
    term();
    setState(992);
    term();
    setState(993);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- T_valuation_pairContext ------------------------------------------------------------------

SMTLIBv2Parser::T_valuation_pairContext::T_valuation_pairContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::T_valuation_pairContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::T_valuation_pairContext::symbol() {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(0);
}

SMTLIBv2Parser::B_valueContext* SMTLIBv2Parser::T_valuation_pairContext::b_value() {
  return getRuleContext<SMTLIBv2Parser::B_valueContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::T_valuation_pairContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::T_valuation_pairContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleT_valuation_pair;
}

antlrcpp::Any SMTLIBv2Parser::T_valuation_pairContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitT_valuation_pair(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::T_valuation_pairContext* SMTLIBv2Parser::t_valuation_pair() {
  T_valuation_pairContext *_localctx = _tracker.createInstance<T_valuation_pairContext>(_ctx, getState());
  enterRule(_localctx, 164, SMTLIBv2Parser::RuleT_valuation_pair);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(995);
    match(SMTLIBv2Parser::ParOpen);
    setState(996);
    symbol();
    setState(997);
    b_value();
    setState(998);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Check_sat_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Check_sat_responseContext::Check_sat_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Check_sat_responseContext::PS_Sat() {
  return getToken(SMTLIBv2Parser::PS_Sat, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Check_sat_responseContext::PS_Unsat() {
  return getToken(SMTLIBv2Parser::PS_Unsat, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Check_sat_responseContext::PS_Unknown() {
  return getToken(SMTLIBv2Parser::PS_Unknown, 0);
}


size_t SMTLIBv2Parser::Check_sat_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleCheck_sat_response;
}

antlrcpp::Any SMTLIBv2Parser::Check_sat_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitCheck_sat_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Check_sat_responseContext* SMTLIBv2Parser::check_sat_response() {
  Check_sat_responseContext *_localctx = _tracker.createInstance<Check_sat_responseContext>(_ctx, getState());
  enterRule(_localctx, 166, SMTLIBv2Parser::RuleCheck_sat_response);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1000);
    _la = _input->LA(1);
    if (!((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::PS_Sat)
      | (1ULL << SMTLIBv2Parser::PS_Unknown)
      | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0))) {
    _errHandler->recoverInline(this);
    }
    else {
      _errHandler->reportMatch(this);
      consume();
    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Echo_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Echo_responseContext::Echo_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::StringContext* SMTLIBv2Parser::Echo_responseContext::string() {
  return getRuleContext<SMTLIBv2Parser::StringContext>(0);
}


size_t SMTLIBv2Parser::Echo_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleEcho_response;
}

antlrcpp::Any SMTLIBv2Parser::Echo_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitEcho_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Echo_responseContext* SMTLIBv2Parser::echo_response() {
  Echo_responseContext *_localctx = _tracker.createInstance<Echo_responseContext>(_ctx, getState());
  enterRule(_localctx, 168, SMTLIBv2Parser::RuleEcho_response);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1002);
    string();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Get_assertions_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Get_assertions_responseContext::Get_assertions_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Get_assertions_responseContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Get_assertions_responseContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::TermContext *> SMTLIBv2Parser::Get_assertions_responseContext::term() {
  return getRuleContexts<SMTLIBv2Parser::TermContext>();
}

SMTLIBv2Parser::TermContext* SMTLIBv2Parser::Get_assertions_responseContext::term(size_t i) {
  return getRuleContext<SMTLIBv2Parser::TermContext>(i);
}


size_t SMTLIBv2Parser::Get_assertions_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGet_assertions_response;
}

antlrcpp::Any SMTLIBv2Parser::Get_assertions_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGet_assertions_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Get_assertions_responseContext* SMTLIBv2Parser::get_assertions_response() {
  Get_assertions_responseContext *_localctx = _tracker.createInstance<Get_assertions_responseContext>(_ctx, getState());
  enterRule(_localctx, 170, SMTLIBv2Parser::RuleGet_assertions_response);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1004);
    match(SMTLIBv2Parser::ParOpen);
    setState(1008);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::ParOpen)
      | (1ULL << SMTLIBv2Parser::String)
      | (1ULL << SMTLIBv2Parser::QuotedSymbol)
      | (1ULL << SMTLIBv2Parser::PS_Not)
      | (1ULL << SMTLIBv2Parser::PS_Bool)
      | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
      | (1ULL << SMTLIBv2Parser::PS_Error)
      | (1ULL << SMTLIBv2Parser::PS_False)
      | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
      | (1ULL << SMTLIBv2Parser::PS_Incomplete)
      | (1ULL << SMTLIBv2Parser::PS_Logic)
      | (1ULL << SMTLIBv2Parser::PS_Memout)
      | (1ULL << SMTLIBv2Parser::PS_Sat)
      | (1ULL << SMTLIBv2Parser::PS_Success)
      | (1ULL << SMTLIBv2Parser::PS_Theory)
      | (1ULL << SMTLIBv2Parser::PS_True)
      | (1ULL << SMTLIBv2Parser::PS_Unknown)
      | (1ULL << SMTLIBv2Parser::PS_Unsupported)
      | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || ((((_la - 66) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 66)) & ((1ULL << (SMTLIBv2Parser::Numeral - 66))
      | (1ULL << (SMTLIBv2Parser::Binary - 66))
      | (1ULL << (SMTLIBv2Parser::HexDecimal - 66))
      | (1ULL << (SMTLIBv2Parser::Decimal - 66))
      | (1ULL << (SMTLIBv2Parser::UndefinedSymbol - 66)))) != 0)) {
      setState(1005);
      term();
      setState(1010);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(1011);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Get_assignment_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Get_assignment_responseContext::Get_assignment_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Get_assignment_responseContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Get_assignment_responseContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::T_valuation_pairContext *> SMTLIBv2Parser::Get_assignment_responseContext::t_valuation_pair() {
  return getRuleContexts<SMTLIBv2Parser::T_valuation_pairContext>();
}

SMTLIBv2Parser::T_valuation_pairContext* SMTLIBv2Parser::Get_assignment_responseContext::t_valuation_pair(size_t i) {
  return getRuleContext<SMTLIBv2Parser::T_valuation_pairContext>(i);
}


size_t SMTLIBv2Parser::Get_assignment_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGet_assignment_response;
}

antlrcpp::Any SMTLIBv2Parser::Get_assignment_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGet_assignment_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Get_assignment_responseContext* SMTLIBv2Parser::get_assignment_response() {
  Get_assignment_responseContext *_localctx = _tracker.createInstance<Get_assignment_responseContext>(_ctx, getState());
  enterRule(_localctx, 172, SMTLIBv2Parser::RuleGet_assignment_response);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1013);
    match(SMTLIBv2Parser::ParOpen);
    setState(1017);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SMTLIBv2Parser::ParOpen) {
      setState(1014);
      t_valuation_pair();
      setState(1019);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(1020);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Get_info_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Get_info_responseContext::Get_info_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Get_info_responseContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Get_info_responseContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::Info_responseContext *> SMTLIBv2Parser::Get_info_responseContext::info_response() {
  return getRuleContexts<SMTLIBv2Parser::Info_responseContext>();
}

SMTLIBv2Parser::Info_responseContext* SMTLIBv2Parser::Get_info_responseContext::info_response(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Info_responseContext>(i);
}


size_t SMTLIBv2Parser::Get_info_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGet_info_response;
}

antlrcpp::Any SMTLIBv2Parser::Get_info_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGet_info_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Get_info_responseContext* SMTLIBv2Parser::get_info_response() {
  Get_info_responseContext *_localctx = _tracker.createInstance<Get_info_responseContext>(_ctx, getState());
  enterRule(_localctx, 174, SMTLIBv2Parser::RuleGet_info_response);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1022);
    match(SMTLIBv2Parser::ParOpen);
    setState(1024); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(1023);
      info_response();
      setState(1026); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (((((_la - 70) & ~ 0x3fULL) == 0) &&
      ((1ULL << (_la - 70)) & ((1ULL << (SMTLIBv2Parser::Colon - 70))
      | (1ULL << (SMTLIBv2Parser::PK_AllStatistics - 70))
      | (1ULL << (SMTLIBv2Parser::PK_AssertionStackLevels - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Authors - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Category - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Chainable - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Definition - 70))
      | (1ULL << (SMTLIBv2Parser::PK_DiagnosticOutputChannel - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ErrorBehaviour - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Extension - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Funs - 70))
      | (1ULL << (SMTLIBv2Parser::PK_FunsDescription - 70))
      | (1ULL << (SMTLIBv2Parser::PK_GlobalDeclarations - 70))
      | (1ULL << (SMTLIBv2Parser::PK_InteractiveMode - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Language - 70))
      | (1ULL << (SMTLIBv2Parser::PK_LeftAssoc - 70))
      | (1ULL << (SMTLIBv2Parser::PK_License - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Named - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Name - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Notes - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Pattern - 70))
      | (1ULL << (SMTLIBv2Parser::PK_PrintSuccess - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssertions - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceAssignments - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceModels - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceProofs - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatAssumptions - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ProduceUnsatCores - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RandomSeed - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ReasonUnknown - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RegularOutputChannel - 70))
      | (1ULL << (SMTLIBv2Parser::PK_ReproducibleResourceLimit - 70))
      | (1ULL << (SMTLIBv2Parser::PK_RightAssoc - 70))
      | (1ULL << (SMTLIBv2Parser::PK_SmtLibVersion - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Sorts - 70))
      | (1ULL << (SMTLIBv2Parser::PK_SortsDescription - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Source - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Status - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Theories - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Values - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Verbosity - 70))
      | (1ULL << (SMTLIBv2Parser::PK_Version - 70)))) != 0));
    setState(1028);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Get_model_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Get_model_responseContext::Get_model_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Get_model_responseContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Get_model_responseContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::Model_responseContext *> SMTLIBv2Parser::Get_model_responseContext::model_response() {
  return getRuleContexts<SMTLIBv2Parser::Model_responseContext>();
}

SMTLIBv2Parser::Model_responseContext* SMTLIBv2Parser::Get_model_responseContext::model_response(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Model_responseContext>(i);
}


size_t SMTLIBv2Parser::Get_model_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGet_model_response;
}

antlrcpp::Any SMTLIBv2Parser::Get_model_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGet_model_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Get_model_responseContext* SMTLIBv2Parser::get_model_response() {
  Get_model_responseContext *_localctx = _tracker.createInstance<Get_model_responseContext>(_ctx, getState());
  enterRule(_localctx, 176, SMTLIBv2Parser::RuleGet_model_response);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1030);
    match(SMTLIBv2Parser::ParOpen);
    setState(1034);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while (_la == SMTLIBv2Parser::ParOpen) {
      setState(1031);
      model_response();
      setState(1036);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(1037);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Get_option_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Get_option_responseContext::Get_option_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::Attribute_valueContext* SMTLIBv2Parser::Get_option_responseContext::attribute_value() {
  return getRuleContext<SMTLIBv2Parser::Attribute_valueContext>(0);
}


size_t SMTLIBv2Parser::Get_option_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGet_option_response;
}

antlrcpp::Any SMTLIBv2Parser::Get_option_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGet_option_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Get_option_responseContext* SMTLIBv2Parser::get_option_response() {
  Get_option_responseContext *_localctx = _tracker.createInstance<Get_option_responseContext>(_ctx, getState());
  enterRule(_localctx, 178, SMTLIBv2Parser::RuleGet_option_response);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1039);
    attribute_value();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Get_proof_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Get_proof_responseContext::Get_proof_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::S_exprContext* SMTLIBv2Parser::Get_proof_responseContext::s_expr() {
  return getRuleContext<SMTLIBv2Parser::S_exprContext>(0);
}


size_t SMTLIBv2Parser::Get_proof_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGet_proof_response;
}

antlrcpp::Any SMTLIBv2Parser::Get_proof_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGet_proof_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Get_proof_responseContext* SMTLIBv2Parser::get_proof_response() {
  Get_proof_responseContext *_localctx = _tracker.createInstance<Get_proof_responseContext>(_ctx, getState());
  enterRule(_localctx, 180, SMTLIBv2Parser::RuleGet_proof_response);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1041);
    s_expr();
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Get_unsat_assump_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Get_unsat_assump_responseContext::Get_unsat_assump_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Get_unsat_assump_responseContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Get_unsat_assump_responseContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::SymbolContext *> SMTLIBv2Parser::Get_unsat_assump_responseContext::symbol() {
  return getRuleContexts<SMTLIBv2Parser::SymbolContext>();
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Get_unsat_assump_responseContext::symbol(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(i);
}


size_t SMTLIBv2Parser::Get_unsat_assump_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGet_unsat_assump_response;
}

antlrcpp::Any SMTLIBv2Parser::Get_unsat_assump_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGet_unsat_assump_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Get_unsat_assump_responseContext* SMTLIBv2Parser::get_unsat_assump_response() {
  Get_unsat_assump_responseContext *_localctx = _tracker.createInstance<Get_unsat_assump_responseContext>(_ctx, getState());
  enterRule(_localctx, 182, SMTLIBv2Parser::RuleGet_unsat_assump_response);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1043);
    match(SMTLIBv2Parser::ParOpen);
    setState(1047);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::QuotedSymbol)
      | (1ULL << SMTLIBv2Parser::PS_Not)
      | (1ULL << SMTLIBv2Parser::PS_Bool)
      | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
      | (1ULL << SMTLIBv2Parser::PS_Error)
      | (1ULL << SMTLIBv2Parser::PS_False)
      | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
      | (1ULL << SMTLIBv2Parser::PS_Incomplete)
      | (1ULL << SMTLIBv2Parser::PS_Logic)
      | (1ULL << SMTLIBv2Parser::PS_Memout)
      | (1ULL << SMTLIBv2Parser::PS_Sat)
      | (1ULL << SMTLIBv2Parser::PS_Success)
      | (1ULL << SMTLIBv2Parser::PS_Theory)
      | (1ULL << SMTLIBv2Parser::PS_True)
      | (1ULL << SMTLIBv2Parser::PS_Unknown)
      | (1ULL << SMTLIBv2Parser::PS_Unsupported)
      | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol) {
      setState(1044);
      symbol();
      setState(1049);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(1050);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Get_unsat_core_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Get_unsat_core_responseContext::Get_unsat_core_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Get_unsat_core_responseContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Get_unsat_core_responseContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::SymbolContext *> SMTLIBv2Parser::Get_unsat_core_responseContext::symbol() {
  return getRuleContexts<SMTLIBv2Parser::SymbolContext>();
}

SMTLIBv2Parser::SymbolContext* SMTLIBv2Parser::Get_unsat_core_responseContext::symbol(size_t i) {
  return getRuleContext<SMTLIBv2Parser::SymbolContext>(i);
}


size_t SMTLIBv2Parser::Get_unsat_core_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGet_unsat_core_response;
}

antlrcpp::Any SMTLIBv2Parser::Get_unsat_core_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGet_unsat_core_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Get_unsat_core_responseContext* SMTLIBv2Parser::get_unsat_core_response() {
  Get_unsat_core_responseContext *_localctx = _tracker.createInstance<Get_unsat_core_responseContext>(_ctx, getState());
  enterRule(_localctx, 184, SMTLIBv2Parser::RuleGet_unsat_core_response);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1052);
    match(SMTLIBv2Parser::ParOpen);
    setState(1056);
    _errHandler->sync(this);
    _la = _input->LA(1);
    while ((((_la & ~ 0x3fULL) == 0) &&
      ((1ULL << _la) & ((1ULL << SMTLIBv2Parser::QuotedSymbol)
      | (1ULL << SMTLIBv2Parser::PS_Not)
      | (1ULL << SMTLIBv2Parser::PS_Bool)
      | (1ULL << SMTLIBv2Parser::PS_ContinuedExecution)
      | (1ULL << SMTLIBv2Parser::PS_Error)
      | (1ULL << SMTLIBv2Parser::PS_False)
      | (1ULL << SMTLIBv2Parser::PS_ImmediateExit)
      | (1ULL << SMTLIBv2Parser::PS_Incomplete)
      | (1ULL << SMTLIBv2Parser::PS_Logic)
      | (1ULL << SMTLIBv2Parser::PS_Memout)
      | (1ULL << SMTLIBv2Parser::PS_Sat)
      | (1ULL << SMTLIBv2Parser::PS_Success)
      | (1ULL << SMTLIBv2Parser::PS_Theory)
      | (1ULL << SMTLIBv2Parser::PS_True)
      | (1ULL << SMTLIBv2Parser::PS_Unknown)
      | (1ULL << SMTLIBv2Parser::PS_Unsupported)
      | (1ULL << SMTLIBv2Parser::PS_Unsat))) != 0) || _la == SMTLIBv2Parser::UndefinedSymbol) {
      setState(1053);
      symbol();
      setState(1058);
      _errHandler->sync(this);
      _la = _input->LA(1);
    }
    setState(1059);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Get_value_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Get_value_responseContext::Get_value_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::Get_value_responseContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::Get_value_responseContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}

std::vector<SMTLIBv2Parser::Valuation_pairContext *> SMTLIBv2Parser::Get_value_responseContext::valuation_pair() {
  return getRuleContexts<SMTLIBv2Parser::Valuation_pairContext>();
}

SMTLIBv2Parser::Valuation_pairContext* SMTLIBv2Parser::Get_value_responseContext::valuation_pair(size_t i) {
  return getRuleContext<SMTLIBv2Parser::Valuation_pairContext>(i);
}


size_t SMTLIBv2Parser::Get_value_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGet_value_response;
}

antlrcpp::Any SMTLIBv2Parser::Get_value_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGet_value_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Get_value_responseContext* SMTLIBv2Parser::get_value_response() {
  Get_value_responseContext *_localctx = _tracker.createInstance<Get_value_responseContext>(_ctx, getState());
  enterRule(_localctx, 186, SMTLIBv2Parser::RuleGet_value_response);
  size_t _la = 0;

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    enterOuterAlt(_localctx, 1);
    setState(1061);
    match(SMTLIBv2Parser::ParOpen);
    setState(1063); 
    _errHandler->sync(this);
    _la = _input->LA(1);
    do {
      setState(1062);
      valuation_pair();
      setState(1065); 
      _errHandler->sync(this);
      _la = _input->LA(1);
    } while (_la == SMTLIBv2Parser::ParOpen);
    setState(1067);
    match(SMTLIBv2Parser::ParClose);
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- Specific_success_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::Specific_success_responseContext::Specific_success_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

SMTLIBv2Parser::Check_sat_responseContext* SMTLIBv2Parser::Specific_success_responseContext::check_sat_response() {
  return getRuleContext<SMTLIBv2Parser::Check_sat_responseContext>(0);
}

SMTLIBv2Parser::Echo_responseContext* SMTLIBv2Parser::Specific_success_responseContext::echo_response() {
  return getRuleContext<SMTLIBv2Parser::Echo_responseContext>(0);
}

SMTLIBv2Parser::Get_assertions_responseContext* SMTLIBv2Parser::Specific_success_responseContext::get_assertions_response() {
  return getRuleContext<SMTLIBv2Parser::Get_assertions_responseContext>(0);
}

SMTLIBv2Parser::Get_assignment_responseContext* SMTLIBv2Parser::Specific_success_responseContext::get_assignment_response() {
  return getRuleContext<SMTLIBv2Parser::Get_assignment_responseContext>(0);
}

SMTLIBv2Parser::Get_info_responseContext* SMTLIBv2Parser::Specific_success_responseContext::get_info_response() {
  return getRuleContext<SMTLIBv2Parser::Get_info_responseContext>(0);
}

SMTLIBv2Parser::Get_model_responseContext* SMTLIBv2Parser::Specific_success_responseContext::get_model_response() {
  return getRuleContext<SMTLIBv2Parser::Get_model_responseContext>(0);
}

SMTLIBv2Parser::Get_option_responseContext* SMTLIBv2Parser::Specific_success_responseContext::get_option_response() {
  return getRuleContext<SMTLIBv2Parser::Get_option_responseContext>(0);
}

SMTLIBv2Parser::Get_proof_responseContext* SMTLIBv2Parser::Specific_success_responseContext::get_proof_response() {
  return getRuleContext<SMTLIBv2Parser::Get_proof_responseContext>(0);
}

SMTLIBv2Parser::Get_unsat_assump_responseContext* SMTLIBv2Parser::Specific_success_responseContext::get_unsat_assump_response() {
  return getRuleContext<SMTLIBv2Parser::Get_unsat_assump_responseContext>(0);
}

SMTLIBv2Parser::Get_unsat_core_responseContext* SMTLIBv2Parser::Specific_success_responseContext::get_unsat_core_response() {
  return getRuleContext<SMTLIBv2Parser::Get_unsat_core_responseContext>(0);
}

SMTLIBv2Parser::Get_value_responseContext* SMTLIBv2Parser::Specific_success_responseContext::get_value_response() {
  return getRuleContext<SMTLIBv2Parser::Get_value_responseContext>(0);
}


size_t SMTLIBv2Parser::Specific_success_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleSpecific_success_response;
}

antlrcpp::Any SMTLIBv2Parser::Specific_success_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitSpecific_success_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::Specific_success_responseContext* SMTLIBv2Parser::specific_success_response() {
  Specific_success_responseContext *_localctx = _tracker.createInstance<Specific_success_responseContext>(_ctx, getState());
  enterRule(_localctx, 188, SMTLIBv2Parser::RuleSpecific_success_response);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(1080);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 72, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(1069);
      check_sat_response();
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(1070);
      echo_response();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(1071);
      get_assertions_response();
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(1072);
      get_assignment_response();
      break;
    }

    case 5: {
      enterOuterAlt(_localctx, 5);
      setState(1073);
      get_info_response();
      break;
    }

    case 6: {
      enterOuterAlt(_localctx, 6);
      setState(1074);
      get_model_response();
      break;
    }

    case 7: {
      enterOuterAlt(_localctx, 7);
      setState(1075);
      get_option_response();
      break;
    }

    case 8: {
      enterOuterAlt(_localctx, 8);
      setState(1076);
      get_proof_response();
      break;
    }

    case 9: {
      enterOuterAlt(_localctx, 9);
      setState(1077);
      get_unsat_assump_response();
      break;
    }

    case 10: {
      enterOuterAlt(_localctx, 10);
      setState(1078);
      get_unsat_core_response();
      break;
    }

    case 11: {
      enterOuterAlt(_localctx, 11);
      setState(1079);
      get_value_response();
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

//----------------- General_responseContext ------------------------------------------------------------------

SMTLIBv2Parser::General_responseContext::General_responseContext(ParserRuleContext *parent, size_t invokingState)
  : ParserRuleContext(parent, invokingState) {
}

tree::TerminalNode* SMTLIBv2Parser::General_responseContext::PS_Success() {
  return getToken(SMTLIBv2Parser::PS_Success, 0);
}

SMTLIBv2Parser::Specific_success_responseContext* SMTLIBv2Parser::General_responseContext::specific_success_response() {
  return getRuleContext<SMTLIBv2Parser::Specific_success_responseContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::General_responseContext::PS_Unsupported() {
  return getToken(SMTLIBv2Parser::PS_Unsupported, 0);
}

tree::TerminalNode* SMTLIBv2Parser::General_responseContext::ParOpen() {
  return getToken(SMTLIBv2Parser::ParOpen, 0);
}

tree::TerminalNode* SMTLIBv2Parser::General_responseContext::PS_Error() {
  return getToken(SMTLIBv2Parser::PS_Error, 0);
}

SMTLIBv2Parser::StringContext* SMTLIBv2Parser::General_responseContext::string() {
  return getRuleContext<SMTLIBv2Parser::StringContext>(0);
}

tree::TerminalNode* SMTLIBv2Parser::General_responseContext::ParClose() {
  return getToken(SMTLIBv2Parser::ParClose, 0);
}


size_t SMTLIBv2Parser::General_responseContext::getRuleIndex() const {
  return SMTLIBv2Parser::RuleGeneral_response;
}

antlrcpp::Any SMTLIBv2Parser::General_responseContext::accept(tree::ParseTreeVisitor *visitor) {
  if (auto parserVisitor = dynamic_cast<SMTLIBv2Visitor*>(visitor))
    return parserVisitor->visitGeneral_response(this);
  else
    return visitor->visitChildren(this);
}

SMTLIBv2Parser::General_responseContext* SMTLIBv2Parser::general_response() {
  General_responseContext *_localctx = _tracker.createInstance<General_responseContext>(_ctx, getState());
  enterRule(_localctx, 190, SMTLIBv2Parser::RuleGeneral_response);

  auto onExit = finally([=] {
    exitRule();
  });
  try {
    setState(1090);
    _errHandler->sync(this);
    switch (getInterpreter<atn::ParserATNSimulator>()->adaptivePredict(_input, 73, _ctx)) {
    case 1: {
      enterOuterAlt(_localctx, 1);
      setState(1082);
      match(SMTLIBv2Parser::PS_Success);
      break;
    }

    case 2: {
      enterOuterAlt(_localctx, 2);
      setState(1083);
      specific_success_response();
      break;
    }

    case 3: {
      enterOuterAlt(_localctx, 3);
      setState(1084);
      match(SMTLIBv2Parser::PS_Unsupported);
      break;
    }

    case 4: {
      enterOuterAlt(_localctx, 4);
      setState(1085);
      match(SMTLIBv2Parser::ParOpen);
      setState(1086);
      match(SMTLIBv2Parser::PS_Error);
      setState(1087);
      string();
      setState(1088);
      match(SMTLIBv2Parser::ParClose);
      break;
    }

    }
   
  }
  catch (RecognitionException &e) {
    _errHandler->reportError(this, e);
    _localctx->exception = std::current_exception();
    _errHandler->recover(this, _localctx->exception);
  }

  return _localctx;
}

// Static vars and initialization.
std::vector<dfa::DFA> SMTLIBv2Parser::_decisionToDFA;
atn::PredictionContextCache SMTLIBv2Parser::_sharedContextCache;

// We own the ATN which in turn owns the ATN states.
atn::ATN SMTLIBv2Parser::_atn;
std::vector<uint16_t> SMTLIBv2Parser::_serializedATN;

std::vector<std::string> SMTLIBv2Parser::_ruleNames = {
  "start", "response", "generalReservedWord", "simpleSymbol", "quotedSymbol", 
  "predefSymbol", "predefKeyword", "symbol", "numeral", "decimal", "hexadecimal", 
  "binary", "string", "keyword", "spec_constant", "s_expr", "index", "identifier", 
  "attribute_value", "attribute", "sort", "qual_identifer", "var_binding", 
  "sorted_var", "pattern", "match_case", "term", "sort_symbol_decl", "meta_spec_constant", 
  "fun_symbol_decl", "par_fun_symbol_decl", "theory_attribute", "theory_decl", 
  "logic_attribue", "logic", "sort_dec", "selector_dec", "constructor_dec", 
  "datatype_dec", "function_dec", "function_def", "prop_literal", "script", 
  "cmd_assert", "cmd_checkSat", "cmd_checkSatAssuming", "cmd_declareConst", 
  "cmd_declareDatatype", "cmd_declareDatatypes", "cmd_declareFun", "cmd_declareSort", 
  "cmd_defineFun", "cmd_defineFunRec", "cmd_defineFunsRec", "cmd_defineSort", 
  "cmd_echo", "cmd_exit", "cmd_getAssertions", "cmd_getAssignment", "cmd_getInfo", 
  "cmd_getModel", "cmd_getOption", "cmd_getProof", "cmd_getUnsatAssumptions", 
  "cmd_getUnsatCore", "cmd_getValue", "cmd_pop", "cmd_push", "cmd_reset", 
  "cmd_resetAssertions", "cmd_setInfo", "cmd_setLogic", "cmd_setOption", 
  "command", "b_value", "option", "info_flag", "error_behaviour", "reason_unknown", 
  "model_response", "info_response", "valuation_pair", "t_valuation_pair", 
  "check_sat_response", "echo_response", "get_assertions_response", "get_assignment_response", 
  "get_info_response", "get_model_response", "get_option_response", "get_proof_response", 
  "get_unsat_assump_response", "get_unsat_core_response", "get_value_response", 
  "specific_success_response", "general_response"
};

std::vector<std::string> SMTLIBv2Parser::_literalNames = {
  "", "", "'('", "')'", "';'", "", "", "'not'", "'Bool'", "'continued-execution'", 
  "'error'", "'false'", "'immediate-exit'", "'incomplete'", "'logic'", "'memout'", 
  "'sat'", "'success'", "'theory'", "'true'", "'unknown'", "'unsupported'", 
  "'unsat'", "'assert'", "'check-sat'", "'check-sat-assuming'", "'declare-const'", 
  "'declare-datatype'", "'declare-datatypes'", "'declare-fun'", "'declare-sort'", 
  "'define-fun'", "'define-fun-rec'", "'define-funs-rec'", "'define-sort'", 
  "'echo'", "'exit'", "'get-assertions'", "'get-assignment'", "'get-info'", 
  "'get-model'", "'get-option'", "'get-proof'", "'get-unsat-assumptions'", 
  "'get-unsat-core'", "'get-value'", "'pop'", "'push'", "'reset'", "'reset-assertions'", 
  "'set-info'", "'set-logic'", "'set-option'", "'!'", "'_'", "'as'", "'BINARY'", 
  "'DECIMAL'", "'exists'", "'HEXADECIMAL'", "'forall'", "'let'", "'match'", 
  "'NUMERAL'", "'par'", "'string'", "", "", "", "", "':'", "':all-statistics'", 
  "':assertion-stack-levels'", "':authors'", "':category'", "':chainable'", 
  "':definition'", "':diagnostic-output-channel'", "':error-behavior'", 
  "':extensions'", "':funs'", "':funs-description'", "':global-declarations'", 
  "':interactive-mode'", "':language'", "':left-assoc'", "':license'", "':named'", 
  "':name'", "':notes'", "':pattern'", "':print-success'", "':produce-assertions'", 
  "':produce-assignments'", "':produce-models'", "':produce-proofs'", "':produce-unsat-assumptions'", 
  "':produce-unsat-cores'", "':random-seed'", "':reason-unknown'", "':regular-output-channel'", 
  "':reproducible-resource-limit'", "':right-assoc'", "':smt-lib-version'", 
  "':sorts'", "':sorts-description'", "':source'", "':status'", "':theories'", 
  "':values'", "':verbosity'", "':version'"
};

std::vector<std::string> SMTLIBv2Parser::_symbolicNames = {
  "", "Comment", "ParOpen", "ParClose", "Semicolon", "String", "QuotedSymbol", 
  "PS_Not", "PS_Bool", "PS_ContinuedExecution", "PS_Error", "PS_False", 
  "PS_ImmediateExit", "PS_Incomplete", "PS_Logic", "PS_Memout", "PS_Sat", 
  "PS_Success", "PS_Theory", "PS_True", "PS_Unknown", "PS_Unsupported", 
  "PS_Unsat", "CMD_Assert", "CMD_CheckSat", "CMD_CheckSatAssuming", "CMD_DeclareConst", 
  "CMD_DeclareDatatype", "CMD_DeclareDatatypes", "CMD_DeclareFun", "CMD_DeclareSort", 
  "CMD_DefineFun", "CMD_DefineFunRec", "CMD_DefineFunsRec", "CMD_DefineSort", 
  "CMD_Echo", "CMD_Exit", "CMD_GetAssertions", "CMD_GetAssignment", "CMD_GetInfo", 
  "CMD_GetModel", "CMD_GetOption", "CMD_GetProof", "CMD_GetUnsatAssumptions", 
  "CMD_GetUnsatCore", "CMD_GetValue", "CMD_Pop", "CMD_Push", "CMD_Reset", 
  "CMD_ResetAssertions", "CMD_SetInfo", "CMD_SetLogic", "CMD_SetOption", 
  "GRW_Exclamation", "GRW_Underscore", "GRW_As", "GRW_Binary", "GRW_Decimal", 
  "GRW_Exists", "GRW_Hexadecimal", "GRW_Forall", "GRW_Let", "GRW_Match", 
  "GRW_Numeral", "GRW_Par", "GRW_String", "Numeral", "Binary", "HexDecimal", 
  "Decimal", "Colon", "PK_AllStatistics", "PK_AssertionStackLevels", "PK_Authors", 
  "PK_Category", "PK_Chainable", "PK_Definition", "PK_DiagnosticOutputChannel", 
  "PK_ErrorBehaviour", "PK_Extension", "PK_Funs", "PK_FunsDescription", 
  "PK_GlobalDeclarations", "PK_InteractiveMode", "PK_Language", "PK_LeftAssoc", 
  "PK_License", "PK_Named", "PK_Name", "PK_Notes", "PK_Pattern", "PK_PrintSuccess", 
  "PK_ProduceAssertions", "PK_ProduceAssignments", "PK_ProduceModels", "PK_ProduceProofs", 
  "PK_ProduceUnsatAssumptions", "PK_ProduceUnsatCores", "PK_RandomSeed", 
  "PK_ReasonUnknown", "PK_RegularOutputChannel", "PK_ReproducibleResourceLimit", 
  "PK_RightAssoc", "PK_SmtLibVersion", "PK_Sorts", "PK_SortsDescription", 
  "PK_Source", "PK_Status", "PK_Theories", "PK_Values", "PK_Verbosity", 
  "PK_Version", "UndefinedSymbol", "WS"
};

dfa::Vocabulary SMTLIBv2Parser::_vocabulary(_literalNames, _symbolicNames);

std::vector<std::string> SMTLIBv2Parser::_tokenNames;

SMTLIBv2Parser::Initializer::Initializer() {
	for (size_t i = 0; i < _symbolicNames.size(); ++i) {
		std::string name = _vocabulary.getLiteralName(i);
		if (name.empty()) {
			name = _vocabulary.getSymbolicName(i);
		}

		if (name.empty()) {
			_tokenNames.push_back("<INVALID>");
		} else {
      _tokenNames.push_back(name);
    }
	}

  _serializedATN = {
    0x3, 0x608b, 0xa72a, 0x8133, 0xb9ed, 0x417c, 0x3be7, 0x7786, 0x5964, 
    0x3, 0x73, 0x447, 0x4, 0x2, 0x9, 0x2, 0x4, 0x3, 0x9, 0x3, 0x4, 0x4, 
    0x9, 0x4, 0x4, 0x5, 0x9, 0x5, 0x4, 0x6, 0x9, 0x6, 0x4, 0x7, 0x9, 0x7, 
    0x4, 0x8, 0x9, 0x8, 0x4, 0x9, 0x9, 0x9, 0x4, 0xa, 0x9, 0xa, 0x4, 0xb, 
    0x9, 0xb, 0x4, 0xc, 0x9, 0xc, 0x4, 0xd, 0x9, 0xd, 0x4, 0xe, 0x9, 0xe, 
    0x4, 0xf, 0x9, 0xf, 0x4, 0x10, 0x9, 0x10, 0x4, 0x11, 0x9, 0x11, 0x4, 
    0x12, 0x9, 0x12, 0x4, 0x13, 0x9, 0x13, 0x4, 0x14, 0x9, 0x14, 0x4, 0x15, 
    0x9, 0x15, 0x4, 0x16, 0x9, 0x16, 0x4, 0x17, 0x9, 0x17, 0x4, 0x18, 0x9, 
    0x18, 0x4, 0x19, 0x9, 0x19, 0x4, 0x1a, 0x9, 0x1a, 0x4, 0x1b, 0x9, 0x1b, 
    0x4, 0x1c, 0x9, 0x1c, 0x4, 0x1d, 0x9, 0x1d, 0x4, 0x1e, 0x9, 0x1e, 0x4, 
    0x1f, 0x9, 0x1f, 0x4, 0x20, 0x9, 0x20, 0x4, 0x21, 0x9, 0x21, 0x4, 0x22, 
    0x9, 0x22, 0x4, 0x23, 0x9, 0x23, 0x4, 0x24, 0x9, 0x24, 0x4, 0x25, 0x9, 
    0x25, 0x4, 0x26, 0x9, 0x26, 0x4, 0x27, 0x9, 0x27, 0x4, 0x28, 0x9, 0x28, 
    0x4, 0x29, 0x9, 0x29, 0x4, 0x2a, 0x9, 0x2a, 0x4, 0x2b, 0x9, 0x2b, 0x4, 
    0x2c, 0x9, 0x2c, 0x4, 0x2d, 0x9, 0x2d, 0x4, 0x2e, 0x9, 0x2e, 0x4, 0x2f, 
    0x9, 0x2f, 0x4, 0x30, 0x9, 0x30, 0x4, 0x31, 0x9, 0x31, 0x4, 0x32, 0x9, 
    0x32, 0x4, 0x33, 0x9, 0x33, 0x4, 0x34, 0x9, 0x34, 0x4, 0x35, 0x9, 0x35, 
    0x4, 0x36, 0x9, 0x36, 0x4, 0x37, 0x9, 0x37, 0x4, 0x38, 0x9, 0x38, 0x4, 
    0x39, 0x9, 0x39, 0x4, 0x3a, 0x9, 0x3a, 0x4, 0x3b, 0x9, 0x3b, 0x4, 0x3c, 
    0x9, 0x3c, 0x4, 0x3d, 0x9, 0x3d, 0x4, 0x3e, 0x9, 0x3e, 0x4, 0x3f, 0x9, 
    0x3f, 0x4, 0x40, 0x9, 0x40, 0x4, 0x41, 0x9, 0x41, 0x4, 0x42, 0x9, 0x42, 
    0x4, 0x43, 0x9, 0x43, 0x4, 0x44, 0x9, 0x44, 0x4, 0x45, 0x9, 0x45, 0x4, 
    0x46, 0x9, 0x46, 0x4, 0x47, 0x9, 0x47, 0x4, 0x48, 0x9, 0x48, 0x4, 0x49, 
    0x9, 0x49, 0x4, 0x4a, 0x9, 0x4a, 0x4, 0x4b, 0x9, 0x4b, 0x4, 0x4c, 0x9, 
    0x4c, 0x4, 0x4d, 0x9, 0x4d, 0x4, 0x4e, 0x9, 0x4e, 0x4, 0x4f, 0x9, 0x4f, 
    0x4, 0x50, 0x9, 0x50, 0x4, 0x51, 0x9, 0x51, 0x4, 0x52, 0x9, 0x52, 0x4, 
    0x53, 0x9, 0x53, 0x4, 0x54, 0x9, 0x54, 0x4, 0x55, 0x9, 0x55, 0x4, 0x56, 
    0x9, 0x56, 0x4, 0x57, 0x9, 0x57, 0x4, 0x58, 0x9, 0x58, 0x4, 0x59, 0x9, 
    0x59, 0x4, 0x5a, 0x9, 0x5a, 0x4, 0x5b, 0x9, 0x5b, 0x4, 0x5c, 0x9, 0x5c, 
    0x4, 0x5d, 0x9, 0x5d, 0x4, 0x5e, 0x9, 0x5e, 0x4, 0x5f, 0x9, 0x5f, 0x4, 
    0x60, 0x9, 0x60, 0x4, 0x61, 0x9, 0x61, 0x3, 0x2, 0x3, 0x2, 0x3, 0x2, 
    0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x3, 0x4, 0x3, 0x4, 0x3, 0x5, 0x3, 0x5, 
    0x5, 0x5, 0xcd, 0xa, 0x5, 0x3, 0x6, 0x3, 0x6, 0x3, 0x7, 0x3, 0x7, 0x3, 
    0x8, 0x3, 0x8, 0x3, 0x9, 0x3, 0x9, 0x5, 0x9, 0xd7, 0xa, 0x9, 0x3, 0xa, 
    0x3, 0xa, 0x3, 0xb, 0x3, 0xb, 0x3, 0xc, 0x3, 0xc, 0x3, 0xd, 0x3, 0xd, 
    0x3, 0xe, 0x3, 0xe, 0x3, 0xf, 0x3, 0xf, 0x3, 0xf, 0x5, 0xf, 0xe6, 0xa, 
    0xf, 0x3, 0x10, 0x3, 0x10, 0x3, 0x10, 0x3, 0x10, 0x3, 0x10, 0x5, 0x10, 
    0xed, 0xa, 0x10, 0x3, 0x11, 0x3, 0x11, 0x3, 0x11, 0x3, 0x11, 0x3, 0x11, 
    0x7, 0x11, 0xf4, 0xa, 0x11, 0xc, 0x11, 0xe, 0x11, 0xf7, 0xb, 0x11, 0x3, 
    0x11, 0x5, 0x11, 0xfa, 0xa, 0x11, 0x3, 0x12, 0x3, 0x12, 0x5, 0x12, 0xfe, 
    0xa, 0x12, 0x3, 0x13, 0x3, 0x13, 0x3, 0x13, 0x3, 0x13, 0x3, 0x13, 0x6, 
    0x13, 0x105, 0xa, 0x13, 0xd, 0x13, 0xe, 0x13, 0x106, 0x3, 0x13, 0x3, 
    0x13, 0x5, 0x13, 0x10b, 0xa, 0x13, 0x3, 0x14, 0x3, 0x14, 0x3, 0x14, 
    0x3, 0x14, 0x7, 0x14, 0x111, 0xa, 0x14, 0xc, 0x14, 0xe, 0x14, 0x114, 
    0xb, 0x14, 0x3, 0x14, 0x5, 0x14, 0x117, 0xa, 0x14, 0x3, 0x15, 0x3, 0x15, 
    0x3, 0x15, 0x3, 0x15, 0x5, 0x15, 0x11d, 0xa, 0x15, 0x3, 0x16, 0x3, 0x16, 
    0x3, 0x16, 0x3, 0x16, 0x6, 0x16, 0x123, 0xa, 0x16, 0xd, 0x16, 0xe, 0x16, 
    0x124, 0x3, 0x16, 0x3, 0x16, 0x5, 0x16, 0x129, 0xa, 0x16, 0x3, 0x17, 
    0x3, 0x17, 0x3, 0x17, 0x3, 0x17, 0x3, 0x17, 0x3, 0x17, 0x3, 0x17, 0x5, 
    0x17, 0x132, 0xa, 0x17, 0x3, 0x18, 0x3, 0x18, 0x3, 0x18, 0x3, 0x18, 
    0x3, 0x18, 0x3, 0x19, 0x3, 0x19, 0x3, 0x19, 0x3, 0x19, 0x3, 0x19, 0x3, 
    0x1a, 0x3, 0x1a, 0x3, 0x1a, 0x3, 0x1a, 0x6, 0x1a, 0x142, 0xa, 0x1a, 
    0xd, 0x1a, 0xe, 0x1a, 0x143, 0x3, 0x1a, 0x3, 0x1a, 0x5, 0x1a, 0x148, 
    0xa, 0x1a, 0x3, 0x1b, 0x3, 0x1b, 0x3, 0x1b, 0x3, 0x1b, 0x3, 0x1b, 0x3, 
    0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x6, 0x1c, 0x154, 
    0xa, 0x1c, 0xd, 0x1c, 0xe, 0x1c, 0x155, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x6, 0x1c, 0x15e, 0xa, 0x1c, 0xd, 0x1c, 
    0xe, 0x1c, 0x15f, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x6, 0x1c, 0x16a, 0xa, 0x1c, 0xd, 0x1c, 
    0xe, 0x1c, 0x16b, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x6, 0x1c, 0x176, 0xa, 0x1c, 0xd, 0x1c, 
    0xe, 0x1c, 0x177, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x6, 0x1c, 0x183, 0xa, 0x1c, 
    0xd, 0x1c, 0xe, 0x1c, 0x184, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 
    0x3, 0x1c, 0x3, 0x1c, 0x3, 0x1c, 0x6, 0x1c, 0x18e, 0xa, 0x1c, 0xd, 0x1c, 
    0xe, 0x1c, 0x18f, 0x3, 0x1c, 0x3, 0x1c, 0x5, 0x1c, 0x194, 0xa, 0x1c, 
    0x3, 0x1d, 0x3, 0x1d, 0x3, 0x1d, 0x3, 0x1d, 0x7, 0x1d, 0x19a, 0xa, 0x1d, 
    0xc, 0x1d, 0xe, 0x1d, 0x19d, 0xb, 0x1d, 0x3, 0x1d, 0x3, 0x1d, 0x3, 0x1e, 
    0x3, 0x1e, 0x3, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x7, 0x1f, 0x1a7, 
    0xa, 0x1f, 0xc, 0x1f, 0xe, 0x1f, 0x1aa, 0xb, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 
    0x3, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x7, 0x1f, 0x1b2, 0xa, 0x1f, 
    0xc, 0x1f, 0xe, 0x1f, 0x1b5, 0xb, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 
    0x3, 0x1f, 0x3, 0x1f, 0x6, 0x1f, 0x1bc, 0xa, 0x1f, 0xd, 0x1f, 0xe, 0x1f, 
    0x1bd, 0x3, 0x1f, 0x7, 0x1f, 0x1c1, 0xa, 0x1f, 0xc, 0x1f, 0xe, 0x1f, 
    0x1c4, 0xb, 0x1f, 0x3, 0x1f, 0x3, 0x1f, 0x5, 0x1f, 0x1c8, 0xa, 0x1f, 
    0x3, 0x20, 0x3, 0x20, 0x3, 0x20, 0x3, 0x20, 0x3, 0x20, 0x6, 0x20, 0x1cf, 
    0xa, 0x20, 0xd, 0x20, 0xe, 0x20, 0x1d0, 0x3, 0x20, 0x3, 0x20, 0x3, 0x20, 
    0x3, 0x20, 0x6, 0x20, 0x1d7, 0xa, 0x20, 0xd, 0x20, 0xe, 0x20, 0x1d8, 
    0x3, 0x20, 0x7, 0x20, 0x1dc, 0xa, 0x20, 0xc, 0x20, 0xe, 0x20, 0x1df, 
    0xb, 0x20, 0x3, 0x20, 0x3, 0x20, 0x3, 0x20, 0x5, 0x20, 0x1e4, 0xa, 0x20, 
    0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x6, 0x21, 0x1e9, 0xa, 0x21, 0xd, 0x21, 
    0xe, 0x21, 0x1ea, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 
    0x6, 0x21, 0x1f2, 0xa, 0x21, 0xd, 0x21, 0xe, 0x21, 0x1f3, 0x3, 0x21, 
    0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 
    0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x3, 0x21, 0x5, 0x21, 
    0x203, 0xa, 0x21, 0x3, 0x22, 0x3, 0x22, 0x3, 0x22, 0x3, 0x22, 0x6, 0x22, 
    0x209, 0xa, 0x22, 0xd, 0x22, 0xe, 0x22, 0x20a, 0x3, 0x22, 0x3, 0x22, 
    0x3, 0x23, 0x3, 0x23, 0x3, 0x23, 0x6, 0x23, 0x212, 0xa, 0x23, 0xd, 0x23, 
    0xe, 0x23, 0x213, 0x3, 0x23, 0x3, 0x23, 0x3, 0x23, 0x3, 0x23, 0x3, 0x23, 
    0x3, 0x23, 0x3, 0x23, 0x3, 0x23, 0x3, 0x23, 0x3, 0x23, 0x3, 0x23, 0x5, 
    0x23, 0x221, 0xa, 0x23, 0x3, 0x24, 0x3, 0x24, 0x3, 0x24, 0x3, 0x24, 
    0x6, 0x24, 0x227, 0xa, 0x24, 0xd, 0x24, 0xe, 0x24, 0x228, 0x3, 0x24, 
    0x3, 0x24, 0x3, 0x25, 0x3, 0x25, 0x3, 0x25, 0x3, 0x25, 0x3, 0x25, 0x3, 
    0x26, 0x3, 0x26, 0x3, 0x26, 0x3, 0x26, 0x3, 0x26, 0x3, 0x27, 0x3, 0x27, 
    0x3, 0x27, 0x7, 0x27, 0x23a, 0xa, 0x27, 0xc, 0x27, 0xe, 0x27, 0x23d, 
    0xb, 0x27, 0x3, 0x27, 0x3, 0x27, 0x3, 0x28, 0x3, 0x28, 0x6, 0x28, 0x243, 
    0xa, 0x28, 0xd, 0x28, 0xe, 0x28, 0x244, 0x3, 0x28, 0x3, 0x28, 0x3, 0x28, 
    0x3, 0x28, 0x3, 0x28, 0x3, 0x28, 0x6, 0x28, 0x24d, 0xa, 0x28, 0xd, 0x28, 
    0xe, 0x28, 0x24e, 0x3, 0x28, 0x3, 0x28, 0x3, 0x28, 0x6, 0x28, 0x254, 
    0xa, 0x28, 0xd, 0x28, 0xe, 0x28, 0x255, 0x3, 0x28, 0x3, 0x28, 0x3, 0x28, 
    0x5, 0x28, 0x25b, 0xa, 0x28, 0x3, 0x29, 0x3, 0x29, 0x3, 0x29, 0x3, 0x29, 
    0x7, 0x29, 0x261, 0xa, 0x29, 0xc, 0x29, 0xe, 0x29, 0x264, 0xb, 0x29, 
    0x3, 0x29, 0x3, 0x29, 0x3, 0x29, 0x3, 0x29, 0x3, 0x2a, 0x3, 0x2a, 0x3, 
    0x2a, 0x7, 0x2a, 0x26d, 0xa, 0x2a, 0xc, 0x2a, 0xe, 0x2a, 0x270, 0xb, 
    0x2a, 0x3, 0x2a, 0x3, 0x2a, 0x3, 0x2a, 0x3, 0x2a, 0x3, 0x2b, 0x3, 0x2b, 
    0x3, 0x2b, 0x3, 0x2b, 0x3, 0x2b, 0x3, 0x2b, 0x5, 0x2b, 0x27c, 0xa, 0x2b, 
    0x3, 0x2c, 0x7, 0x2c, 0x27f, 0xa, 0x2c, 0xc, 0x2c, 0xe, 0x2c, 0x282, 
    0xb, 0x2c, 0x3, 0x2d, 0x3, 0x2d, 0x3, 0x2e, 0x3, 0x2e, 0x3, 0x2f, 0x3, 
    0x2f, 0x3, 0x30, 0x3, 0x30, 0x3, 0x31, 0x3, 0x31, 0x3, 0x32, 0x3, 0x32, 
    0x3, 0x33, 0x3, 0x33, 0x3, 0x34, 0x3, 0x34, 0x3, 0x35, 0x3, 0x35, 0x3, 
    0x36, 0x3, 0x36, 0x3, 0x37, 0x3, 0x37, 0x3, 0x38, 0x3, 0x38, 0x3, 0x39, 
    0x3, 0x39, 0x3, 0x3a, 0x3, 0x3a, 0x3, 0x3b, 0x3, 0x3b, 0x3, 0x3c, 0x3, 
    0x3c, 0x3, 0x3d, 0x3, 0x3d, 0x3, 0x3e, 0x3, 0x3e, 0x3, 0x3f, 0x3, 0x3f, 
    0x3, 0x40, 0x3, 0x40, 0x3, 0x41, 0x3, 0x41, 0x3, 0x42, 0x3, 0x42, 0x3, 
    0x43, 0x3, 0x43, 0x3, 0x44, 0x3, 0x44, 0x3, 0x45, 0x3, 0x45, 0x3, 0x46, 
    0x3, 0x46, 0x3, 0x47, 0x3, 0x47, 0x3, 0x48, 0x3, 0x48, 0x3, 0x49, 0x3, 
    0x49, 0x3, 0x4a, 0x3, 0x4a, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x6, 0x4b, 
    0x2dd, 0xa, 0x4b, 0xd, 0x4b, 0xe, 0x4b, 0x2de, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x6, 0x4b, 0x2e4, 0xa, 0x4b, 0xd, 0x4b, 0xe, 0x4b, 0x2e5, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x7, 0x4b, 0x2f0, 0xa, 0x4b, 0xc, 0x4b, 0xe, 0x4b, 
    0x2f3, 0xb, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x6, 
    0x4b, 0x30d, 0xa, 0x4b, 0xd, 0x4b, 0xe, 0x4b, 0x30e, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x6, 0x4b, 0x314, 0xa, 0x4b, 0xd, 0x4b, 0xe, 0x4b, 
    0x315, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x7, 0x4b, 0x320, 0xa, 0x4b, 0xc, 0x4b, 0xe, 0x4b, 
    0x323, 0xb, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x6, 0x4b, 0x358, 0xa, 0x4b, 0xd, 0x4b, 0xe, 0x4b, 0x359, 0x3, 
    0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 
    0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 
    0x3, 0x4b, 0x3, 0x4b, 0x3, 0x4b, 0x5, 0x4b, 0x380, 0xa, 0x4b, 0x3, 0x4c, 
    0x3, 0x4c, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 
    0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 
    0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 
    0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 
    0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x3, 0x4d, 0x5, 0x4d, 0x3a1, 0xa, 0x4d, 
    0x3, 0x4e, 0x3, 0x4e, 0x3, 0x4e, 0x3, 0x4e, 0x3, 0x4e, 0x3, 0x4e, 0x3, 
    0x4e, 0x3, 0x4e, 0x5, 0x4e, 0x3ab, 0xa, 0x4e, 0x3, 0x4f, 0x3, 0x4f, 
    0x3, 0x50, 0x3, 0x50, 0x3, 0x50, 0x5, 0x50, 0x3b2, 0xa, 0x50, 0x3, 0x51, 
    0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 
    0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 
    0x6, 0x51, 0x3c2, 0xa, 0x51, 0xd, 0x51, 0xe, 0x51, 0x3c3, 0x3, 0x51, 
    0x3, 0x51, 0x3, 0x51, 0x6, 0x51, 0x3c9, 0xa, 0x51, 0xd, 0x51, 0xe, 0x51, 
    0x3ca, 0x3, 0x51, 0x3, 0x51, 0x3, 0x51, 0x5, 0x51, 0x3d0, 0xa, 0x51, 
    0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 
    0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 0x3, 0x52, 
    0x5, 0x52, 0x3df, 0xa, 0x52, 0x3, 0x53, 0x3, 0x53, 0x3, 0x53, 0x3, 0x53, 
    0x3, 0x53, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 0x54, 0x3, 
    0x55, 0x3, 0x55, 0x3, 0x56, 0x3, 0x56, 0x3, 0x57, 0x3, 0x57, 0x7, 0x57, 
    0x3f1, 0xa, 0x57, 0xc, 0x57, 0xe, 0x57, 0x3f4, 0xb, 0x57, 0x3, 0x57, 
    0x3, 0x57, 0x3, 0x58, 0x3, 0x58, 0x7, 0x58, 0x3fa, 0xa, 0x58, 0xc, 0x58, 
    0xe, 0x58, 0x3fd, 0xb, 0x58, 0x3, 0x58, 0x3, 0x58, 0x3, 0x59, 0x3, 0x59, 
    0x6, 0x59, 0x403, 0xa, 0x59, 0xd, 0x59, 0xe, 0x59, 0x404, 0x3, 0x59, 
    0x3, 0x59, 0x3, 0x5a, 0x3, 0x5a, 0x7, 0x5a, 0x40b, 0xa, 0x5a, 0xc, 0x5a, 
    0xe, 0x5a, 0x40e, 0xb, 0x5a, 0x3, 0x5a, 0x3, 0x5a, 0x3, 0x5b, 0x3, 0x5b, 
    0x3, 0x5c, 0x3, 0x5c, 0x3, 0x5d, 0x3, 0x5d, 0x7, 0x5d, 0x418, 0xa, 0x5d, 
    0xc, 0x5d, 0xe, 0x5d, 0x41b, 0xb, 0x5d, 0x3, 0x5d, 0x3, 0x5d, 0x3, 0x5e, 
    0x3, 0x5e, 0x7, 0x5e, 0x421, 0xa, 0x5e, 0xc, 0x5e, 0xe, 0x5e, 0x424, 
    0xb, 0x5e, 0x3, 0x5e, 0x3, 0x5e, 0x3, 0x5f, 0x3, 0x5f, 0x6, 0x5f, 0x42a, 
    0xa, 0x5f, 0xd, 0x5f, 0xe, 0x5f, 0x42b, 0x3, 0x5f, 0x3, 0x5f, 0x3, 0x60, 
    0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 
    0x60, 0x3, 0x60, 0x3, 0x60, 0x3, 0x60, 0x5, 0x60, 0x43b, 0xa, 0x60, 
    0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 0x61, 0x3, 
    0x61, 0x3, 0x61, 0x5, 0x61, 0x445, 0xa, 0x61, 0x3, 0x61, 0x2, 0x2, 0x62, 
    0x2, 0x4, 0x6, 0x8, 0xa, 0xc, 0xe, 0x10, 0x12, 0x14, 0x16, 0x18, 0x1a, 
    0x1c, 0x1e, 0x20, 0x22, 0x24, 0x26, 0x28, 0x2a, 0x2c, 0x2e, 0x30, 0x32, 
    0x34, 0x36, 0x38, 0x3a, 0x3c, 0x3e, 0x40, 0x42, 0x44, 0x46, 0x48, 0x4a, 
    0x4c, 0x4e, 0x50, 0x52, 0x54, 0x56, 0x58, 0x5a, 0x5c, 0x5e, 0x60, 0x62, 
    0x64, 0x66, 0x68, 0x6a, 0x6c, 0x6e, 0x70, 0x72, 0x74, 0x76, 0x78, 0x7a, 
    0x7c, 0x7e, 0x80, 0x82, 0x84, 0x86, 0x88, 0x8a, 0x8c, 0x8e, 0x90, 0x92, 
    0x94, 0x96, 0x98, 0x9a, 0x9c, 0x9e, 0xa0, 0xa2, 0xa4, 0xa6, 0xa8, 0xaa, 
    0xac, 0xae, 0xb0, 0xb2, 0xb4, 0xb6, 0xb8, 0xba, 0xbc, 0xbe, 0xc0, 0x2, 
    0x9, 0x3, 0x2, 0x37, 0x43, 0x3, 0x2, 0x9, 0x18, 0x3, 0x2, 0x49, 0x71, 
    0x5, 0x2, 0x3b, 0x3b, 0x41, 0x41, 0x43, 0x43, 0x4, 0x2, 0xd, 0xd, 0x15, 
    0x15, 0x4, 0x2, 0xb, 0xb, 0xe, 0xe, 0x5, 0x2, 0x12, 0x12, 0x16, 0x16, 
    0x18, 0x18, 0x2, 0x488, 0x2, 0xc2, 0x3, 0x2, 0x2, 0x2, 0x4, 0xc5, 0x3, 
    0x2, 0x2, 0x2, 0x6, 0xc8, 0x3, 0x2, 0x2, 0x2, 0x8, 0xcc, 0x3, 0x2, 0x2, 
    0x2, 0xa, 0xce, 0x3, 0x2, 0x2, 0x2, 0xc, 0xd0, 0x3, 0x2, 0x2, 0x2, 0xe, 
    0xd2, 0x3, 0x2, 0x2, 0x2, 0x10, 0xd6, 0x3, 0x2, 0x2, 0x2, 0x12, 0xd8, 
    0x3, 0x2, 0x2, 0x2, 0x14, 0xda, 0x3, 0x2, 0x2, 0x2, 0x16, 0xdc, 0x3, 
    0x2, 0x2, 0x2, 0x18, 0xde, 0x3, 0x2, 0x2, 0x2, 0x1a, 0xe0, 0x3, 0x2, 
    0x2, 0x2, 0x1c, 0xe5, 0x3, 0x2, 0x2, 0x2, 0x1e, 0xec, 0x3, 0x2, 0x2, 
    0x2, 0x20, 0xf9, 0x3, 0x2, 0x2, 0x2, 0x22, 0xfd, 0x3, 0x2, 0x2, 0x2, 
    0x24, 0x10a, 0x3, 0x2, 0x2, 0x2, 0x26, 0x116, 0x3, 0x2, 0x2, 0x2, 0x28, 
    0x11c, 0x3, 0x2, 0x2, 0x2, 0x2a, 0x128, 0x3, 0x2, 0x2, 0x2, 0x2c, 0x131, 
    0x3, 0x2, 0x2, 0x2, 0x2e, 0x133, 0x3, 0x2, 0x2, 0x2, 0x30, 0x138, 0x3, 
    0x2, 0x2, 0x2, 0x32, 0x147, 0x3, 0x2, 0x2, 0x2, 0x34, 0x149, 0x3, 0x2, 
    0x2, 0x2, 0x36, 0x193, 0x3, 0x2, 0x2, 0x2, 0x38, 0x195, 0x3, 0x2, 0x2, 
    0x2, 0x3a, 0x1a0, 0x3, 0x2, 0x2, 0x2, 0x3c, 0x1c7, 0x3, 0x2, 0x2, 0x2, 
    0x3e, 0x1e3, 0x3, 0x2, 0x2, 0x2, 0x40, 0x202, 0x3, 0x2, 0x2, 0x2, 0x42, 
    0x204, 0x3, 0x2, 0x2, 0x2, 0x44, 0x220, 0x3, 0x2, 0x2, 0x2, 0x46, 0x222, 
    0x3, 0x2, 0x2, 0x2, 0x48, 0x22c, 0x3, 0x2, 0x2, 0x2, 0x4a, 0x231, 0x3, 
    0x2, 0x2, 0x2, 0x4c, 0x236, 0x3, 0x2, 0x2, 0x2, 0x4e, 0x25a, 0x3, 0x2, 
    0x2, 0x2, 0x50, 0x25c, 0x3, 0x2, 0x2, 0x2, 0x52, 0x269, 0x3, 0x2, 0x2, 
    0x2, 0x54, 0x27b, 0x3, 0x2, 0x2, 0x2, 0x56, 0x280, 0x3, 0x2, 0x2, 0x2, 
    0x58, 0x283, 0x3, 0x2, 0x2, 0x2, 0x5a, 0x285, 0x3, 0x2, 0x2, 0x2, 0x5c, 
    0x287, 0x3, 0x2, 0x2, 0x2, 0x5e, 0x289, 0x3, 0x2, 0x2, 0x2, 0x60, 0x28b, 
    0x3, 0x2, 0x2, 0x2, 0x62, 0x28d, 0x3, 0x2, 0x2, 0x2, 0x64, 0x28f, 0x3, 
    0x2, 0x2, 0x2, 0x66, 0x291, 0x3, 0x2, 0x2, 0x2, 0x68, 0x293, 0x3, 0x2, 
    0x2, 0x2, 0x6a, 0x295, 0x3, 0x2, 0x2, 0x2, 0x6c, 0x297, 0x3, 0x2, 0x2, 
    0x2, 0x6e, 0x299, 0x3, 0x2, 0x2, 0x2, 0x70, 0x29b, 0x3, 0x2, 0x2, 0x2, 
    0x72, 0x29d, 0x3, 0x2, 0x2, 0x2, 0x74, 0x29f, 0x3, 0x2, 0x2, 0x2, 0x76, 
    0x2a1, 0x3, 0x2, 0x2, 0x2, 0x78, 0x2a3, 0x3, 0x2, 0x2, 0x2, 0x7a, 0x2a5, 
    0x3, 0x2, 0x2, 0x2, 0x7c, 0x2a7, 0x3, 0x2, 0x2, 0x2, 0x7e, 0x2a9, 0x3, 
    0x2, 0x2, 0x2, 0x80, 0x2ab, 0x3, 0x2, 0x2, 0x2, 0x82, 0x2ad, 0x3, 0x2, 
    0x2, 0x2, 0x84, 0x2af, 0x3, 0x2, 0x2, 0x2, 0x86, 0x2b1, 0x3, 0x2, 0x2, 
    0x2, 0x88, 0x2b3, 0x3, 0x2, 0x2, 0x2, 0x8a, 0x2b5, 0x3, 0x2, 0x2, 0x2, 
    0x8c, 0x2b7, 0x3, 0x2, 0x2, 0x2, 0x8e, 0x2b9, 0x3, 0x2, 0x2, 0x2, 0x90, 
    0x2bb, 0x3, 0x2, 0x2, 0x2, 0x92, 0x2bd, 0x3, 0x2, 0x2, 0x2, 0x94, 0x37f, 
    0x3, 0x2, 0x2, 0x2, 0x96, 0x381, 0x3, 0x2, 0x2, 0x2, 0x98, 0x3a0, 0x3, 
    0x2, 0x2, 0x2, 0x9a, 0x3aa, 0x3, 0x2, 0x2, 0x2, 0x9c, 0x3ac, 0x3, 0x2, 
    0x2, 0x2, 0x9e, 0x3b1, 0x3, 0x2, 0x2, 0x2, 0xa0, 0x3cf, 0x3, 0x2, 0x2, 
    0x2, 0xa2, 0x3de, 0x3, 0x2, 0x2, 0x2, 0xa4, 0x3e0, 0x3, 0x2, 0x2, 0x2, 
    0xa6, 0x3e5, 0x3, 0x2, 0x2, 0x2, 0xa8, 0x3ea, 0x3, 0x2, 0x2, 0x2, 0xaa, 
    0x3ec, 0x3, 0x2, 0x2, 0x2, 0xac, 0x3ee, 0x3, 0x2, 0x2, 0x2, 0xae, 0x3f7, 
    0x3, 0x2, 0x2, 0x2, 0xb0, 0x400, 0x3, 0x2, 0x2, 0x2, 0xb2, 0x408, 0x3, 
    0x2, 0x2, 0x2, 0xb4, 0x411, 0x3, 0x2, 0x2, 0x2, 0xb6, 0x413, 0x3, 0x2, 
    0x2, 0x2, 0xb8, 0x415, 0x3, 0x2, 0x2, 0x2, 0xba, 0x41e, 0x3, 0x2, 0x2, 
    0x2, 0xbc, 0x427, 0x3, 0x2, 0x2, 0x2, 0xbe, 0x43a, 0x3, 0x2, 0x2, 0x2, 
    0xc0, 0x444, 0x3, 0x2, 0x2, 0x2, 0xc2, 0xc3, 0x5, 0x56, 0x2c, 0x2, 0xc3, 
    0xc4, 0x7, 0x2, 0x2, 0x3, 0xc4, 0x3, 0x3, 0x2, 0x2, 0x2, 0xc5, 0xc6, 
    0x5, 0xc0, 0x61, 0x2, 0xc6, 0xc7, 0x7, 0x2, 0x2, 0x3, 0xc7, 0x5, 0x3, 
    0x2, 0x2, 0x2, 0xc8, 0xc9, 0x9, 0x2, 0x2, 0x2, 0xc9, 0x7, 0x3, 0x2, 
    0x2, 0x2, 0xca, 0xcd, 0x5, 0xc, 0x7, 0x2, 0xcb, 0xcd, 0x7, 0x72, 0x2, 
    0x2, 0xcc, 0xca, 0x3, 0x2, 0x2, 0x2, 0xcc, 0xcb, 0x3, 0x2, 0x2, 0x2, 
    0xcd, 0x9, 0x3, 0x2, 0x2, 0x2, 0xce, 0xcf, 0x7, 0x8, 0x2, 0x2, 0xcf, 
    0xb, 0x3, 0x2, 0x2, 0x2, 0xd0, 0xd1, 0x9, 0x3, 0x2, 0x2, 0xd1, 0xd, 
    0x3, 0x2, 0x2, 0x2, 0xd2, 0xd3, 0x9, 0x4, 0x2, 0x2, 0xd3, 0xf, 0x3, 
    0x2, 0x2, 0x2, 0xd4, 0xd7, 0x5, 0x8, 0x5, 0x2, 0xd5, 0xd7, 0x5, 0xa, 
    0x6, 0x2, 0xd6, 0xd4, 0x3, 0x2, 0x2, 0x2, 0xd6, 0xd5, 0x3, 0x2, 0x2, 
    0x2, 0xd7, 0x11, 0x3, 0x2, 0x2, 0x2, 0xd8, 0xd9, 0x7, 0x44, 0x2, 0x2, 
    0xd9, 0x13, 0x3, 0x2, 0x2, 0x2, 0xda, 0xdb, 0x7, 0x47, 0x2, 0x2, 0xdb, 
    0x15, 0x3, 0x2, 0x2, 0x2, 0xdc, 0xdd, 0x7, 0x46, 0x2, 0x2, 0xdd, 0x17, 
    0x3, 0x2, 0x2, 0x2, 0xde, 0xdf, 0x7, 0x45, 0x2, 0x2, 0xdf, 0x19, 0x3, 
    0x2, 0x2, 0x2, 0xe0, 0xe1, 0x7, 0x7, 0x2, 0x2, 0xe1, 0x1b, 0x3, 0x2, 
    0x2, 0x2, 0xe2, 0xe6, 0x5, 0xe, 0x8, 0x2, 0xe3, 0xe4, 0x7, 0x48, 0x2, 
    0x2, 0xe4, 0xe6, 0x5, 0x8, 0x5, 0x2, 0xe5, 0xe2, 0x3, 0x2, 0x2, 0x2, 
    0xe5, 0xe3, 0x3, 0x2, 0x2, 0x2, 0xe6, 0x1d, 0x3, 0x2, 0x2, 0x2, 0xe7, 
    0xed, 0x5, 0x12, 0xa, 0x2, 0xe8, 0xed, 0x5, 0x14, 0xb, 0x2, 0xe9, 0xed, 
    0x5, 0x16, 0xc, 0x2, 0xea, 0xed, 0x5, 0x18, 0xd, 0x2, 0xeb, 0xed, 0x5, 
    0x1a, 0xe, 0x2, 0xec, 0xe7, 0x3, 0x2, 0x2, 0x2, 0xec, 0xe8, 0x3, 0x2, 
    0x2, 0x2, 0xec, 0xe9, 0x3, 0x2, 0x2, 0x2, 0xec, 0xea, 0x3, 0x2, 0x2, 
    0x2, 0xec, 0xeb, 0x3, 0x2, 0x2, 0x2, 0xed, 0x1f, 0x3, 0x2, 0x2, 0x2, 
    0xee, 0xfa, 0x5, 0x1e, 0x10, 0x2, 0xef, 0xfa, 0x5, 0x10, 0x9, 0x2, 0xf0, 
    0xfa, 0x5, 0x1c, 0xf, 0x2, 0xf1, 0xf5, 0x7, 0x4, 0x2, 0x2, 0xf2, 0xf4, 
    0x5, 0x20, 0x11, 0x2, 0xf3, 0xf2, 0x3, 0x2, 0x2, 0x2, 0xf4, 0xf7, 0x3, 
    0x2, 0x2, 0x2, 0xf5, 0xf3, 0x3, 0x2, 0x2, 0x2, 0xf5, 0xf6, 0x3, 0x2, 
    0x2, 0x2, 0xf6, 0xf8, 0x3, 0x2, 0x2, 0x2, 0xf7, 0xf5, 0x3, 0x2, 0x2, 
    0x2, 0xf8, 0xfa, 0x7, 0x5, 0x2, 0x2, 0xf9, 0xee, 0x3, 0x2, 0x2, 0x2, 
    0xf9, 0xef, 0x3, 0x2, 0x2, 0x2, 0xf9, 0xf0, 0x3, 0x2, 0x2, 0x2, 0xf9, 
    0xf1, 0x3, 0x2, 0x2, 0x2, 0xfa, 0x21, 0x3, 0x2, 0x2, 0x2, 0xfb, 0xfe, 
    0x5, 0x12, 0xa, 0x2, 0xfc, 0xfe, 0x5, 0x10, 0x9, 0x2, 0xfd, 0xfb, 0x3, 
    0x2, 0x2, 0x2, 0xfd, 0xfc, 0x3, 0x2, 0x2, 0x2, 0xfe, 0x23, 0x3, 0x2, 
    0x2, 0x2, 0xff, 0x10b, 0x5, 0x10, 0x9, 0x2, 0x100, 0x101, 0x7, 0x4, 
    0x2, 0x2, 0x101, 0x102, 0x7, 0x38, 0x2, 0x2, 0x102, 0x104, 0x5, 0x10, 
    0x9, 0x2, 0x103, 0x105, 0x5, 0x22, 0x12, 0x2, 0x104, 0x103, 0x3, 0x2, 
    0x2, 0x2, 0x105, 0x106, 0x3, 0x2, 0x2, 0x2, 0x106, 0x104, 0x3, 0x2, 
    0x2, 0x2, 0x106, 0x107, 0x3, 0x2, 0x2, 0x2, 0x107, 0x108, 0x3, 0x2, 
    0x2, 0x2, 0x108, 0x109, 0x7, 0x5, 0x2, 0x2, 0x109, 0x10b, 0x3, 0x2, 
    0x2, 0x2, 0x10a, 0xff, 0x3, 0x2, 0x2, 0x2, 0x10a, 0x100, 0x3, 0x2, 0x2, 
    0x2, 0x10b, 0x25, 0x3, 0x2, 0x2, 0x2, 0x10c, 0x117, 0x5, 0x1e, 0x10, 
    0x2, 0x10d, 0x117, 0x5, 0x10, 0x9, 0x2, 0x10e, 0x112, 0x7, 0x4, 0x2, 
    0x2, 0x10f, 0x111, 0x5, 0x20, 0x11, 0x2, 0x110, 0x10f, 0x3, 0x2, 0x2, 
    0x2, 0x111, 0x114, 0x3, 0x2, 0x2, 0x2, 0x112, 0x110, 0x3, 0x2, 0x2, 
    0x2, 0x112, 0x113, 0x3, 0x2, 0x2, 0x2, 0x113, 0x115, 0x3, 0x2, 0x2, 
    0x2, 0x114, 0x112, 0x3, 0x2, 0x2, 0x2, 0x115, 0x117, 0x7, 0x5, 0x2, 
    0x2, 0x116, 0x10c, 0x3, 0x2, 0x2, 0x2, 0x116, 0x10d, 0x3, 0x2, 0x2, 
    0x2, 0x116, 0x10e, 0x3, 0x2, 0x2, 0x2, 0x117, 0x27, 0x3, 0x2, 0x2, 0x2, 
    0x118, 0x11d, 0x5, 0x1c, 0xf, 0x2, 0x119, 0x11a, 0x5, 0x1c, 0xf, 0x2, 
    0x11a, 0x11b, 0x5, 0x26, 0x14, 0x2, 0x11b, 0x11d, 0x3, 0x2, 0x2, 0x2, 
    0x11c, 0x118, 0x3, 0x2, 0x2, 0x2, 0x11c, 0x119, 0x3, 0x2, 0x2, 0x2, 
    0x11d, 0x29, 0x3, 0x2, 0x2, 0x2, 0x11e, 0x129, 0x5, 0x24, 0x13, 0x2, 
    0x11f, 0x120, 0x7, 0x4, 0x2, 0x2, 0x120, 0x122, 0x5, 0x24, 0x13, 0x2, 
    0x121, 0x123, 0x5, 0x2a, 0x16, 0x2, 0x122, 0x121, 0x3, 0x2, 0x2, 0x2, 
    0x123, 0x124, 0x3, 0x2, 0x2, 0x2, 0x124, 0x122, 0x3, 0x2, 0x2, 0x2, 
    0x124, 0x125, 0x3, 0x2, 0x2, 0x2, 0x125, 0x126, 0x3, 0x2, 0x2, 0x2, 
    0x126, 0x127, 0x7, 0x5, 0x2, 0x2, 0x127, 0x129, 0x3, 0x2, 0x2, 0x2, 
    0x128, 0x11e, 0x3, 0x2, 0x2, 0x2, 0x128, 0x11f, 0x3, 0x2, 0x2, 0x2, 
    0x129, 0x2b, 0x3, 0x2, 0x2, 0x2, 0x12a, 0x132, 0x5, 0x24, 0x13, 0x2, 
    0x12b, 0x12c, 0x7, 0x4, 0x2, 0x2, 0x12c, 0x12d, 0x7, 0x39, 0x2, 0x2, 
    0x12d, 0x12e, 0x5, 0x24, 0x13, 0x2, 0x12e, 0x12f, 0x5, 0x2a, 0x16, 0x2, 
    0x12f, 0x130, 0x7, 0x5, 0x2, 0x2, 0x130, 0x132, 0x3, 0x2, 0x2, 0x2, 
    0x131, 0x12a, 0x3, 0x2, 0x2, 0x2, 0x131, 0x12b, 0x3, 0x2, 0x2, 0x2, 
    0x132, 0x2d, 0x3, 0x2, 0x2, 0x2, 0x133, 0x134, 0x7, 0x4, 0x2, 0x2, 0x134, 
    0x135, 0x5, 0x10, 0x9, 0x2, 0x135, 0x136, 0x5, 0x36, 0x1c, 0x2, 0x136, 
    0x137, 0x7, 0x5, 0x2, 0x2, 0x137, 0x2f, 0x3, 0x2, 0x2, 0x2, 0x138, 0x139, 
    0x7, 0x4, 0x2, 0x2, 0x139, 0x13a, 0x5, 0x10, 0x9, 0x2, 0x13a, 0x13b, 
    0x5, 0x2a, 0x16, 0x2, 0x13b, 0x13c, 0x7, 0x5, 0x2, 0x2, 0x13c, 0x31, 
    0x3, 0x2, 0x2, 0x2, 0x13d, 0x148, 0x5, 0x10, 0x9, 0x2, 0x13e, 0x13f, 
    0x7, 0x4, 0x2, 0x2, 0x13f, 0x141, 0x5, 0x10, 0x9, 0x2, 0x140, 0x142, 
    0x5, 0x10, 0x9, 0x2, 0x141, 0x140, 0x3, 0x2, 0x2, 0x2, 0x142, 0x143, 
    0x3, 0x2, 0x2, 0x2, 0x143, 0x141, 0x3, 0x2, 0x2, 0x2, 0x143, 0x144, 
    0x3, 0x2, 0x2, 0x2, 0x144, 0x145, 0x3, 0x2, 0x2, 0x2, 0x145, 0x146, 
    0x7, 0x5, 0x2, 0x2, 0x146, 0x148, 0x3, 0x2, 0x2, 0x2, 0x147, 0x13d, 
    0x3, 0x2, 0x2, 0x2, 0x147, 0x13e, 0x3, 0x2, 0x2, 0x2, 0x148, 0x33, 0x3, 
    0x2, 0x2, 0x2, 0x149, 0x14a, 0x7, 0x4, 0x2, 0x2, 0x14a, 0x14b, 0x5, 
    0x32, 0x1a, 0x2, 0x14b, 0x14c, 0x5, 0x36, 0x1c, 0x2, 0x14c, 0x14d, 0x7, 
    0x5, 0x2, 0x2, 0x14d, 0x35, 0x3, 0x2, 0x2, 0x2, 0x14e, 0x194, 0x5, 0x1e, 
    0x10, 0x2, 0x14f, 0x194, 0x5, 0x2c, 0x17, 0x2, 0x150, 0x151, 0x7, 0x4, 
    0x2, 0x2, 0x151, 0x153, 0x5, 0x2c, 0x17, 0x2, 0x152, 0x154, 0x5, 0x36, 
    0x1c, 0x2, 0x153, 0x152, 0x3, 0x2, 0x2, 0x2, 0x154, 0x155, 0x3, 0x2, 
    0x2, 0x2, 0x155, 0x153, 0x3, 0x2, 0x2, 0x2, 0x155, 0x156, 0x3, 0x2, 
    0x2, 0x2, 0x156, 0x157, 0x3, 0x2, 0x2, 0x2, 0x157, 0x158, 0x7, 0x5, 
    0x2, 0x2, 0x158, 0x194, 0x3, 0x2, 0x2, 0x2, 0x159, 0x15a, 0x7, 0x4, 
    0x2, 0x2, 0x15a, 0x15b, 0x7, 0x3f, 0x2, 0x2, 0x15b, 0x15d, 0x7, 0x4, 
    0x2, 0x2, 0x15c, 0x15e, 0x5, 0x2e, 0x18, 0x2, 0x15d, 0x15c, 0x3, 0x2, 
    0x2, 0x2, 0x15e, 0x15f, 0x3, 0x2, 0x2, 0x2, 0x15f, 0x15d, 0x3, 0x2, 
    0x2, 0x2, 0x15f, 0x160, 0x3, 0x2, 0x2, 0x2, 0x160, 0x161, 0x3, 0x2, 
    0x2, 0x2, 0x161, 0x162, 0x7, 0x5, 0x2, 0x2, 0x162, 0x163, 0x5, 0x36, 
    0x1c, 0x2, 0x163, 0x164, 0x7, 0x5, 0x2, 0x2, 0x164, 0x194, 0x3, 0x2, 
    0x2, 0x2, 0x165, 0x166, 0x7, 0x4, 0x2, 0x2, 0x166, 0x167, 0x7, 0x3e, 
    0x2, 0x2, 0x167, 0x169, 0x7, 0x4, 0x2, 0x2, 0x168, 0x16a, 0x5, 0x30, 
    0x19, 0x2, 0x169, 0x168, 0x3, 0x2, 0x2, 0x2, 0x16a, 0x16b, 0x3, 0x2, 
    0x2, 0x2, 0x16b, 0x169, 0x3, 0x2, 0x2, 0x2, 0x16b, 0x16c, 0x3, 0x2, 
    0x2, 0x2, 0x16c, 0x16d, 0x3, 0x2, 0x2, 0x2, 0x16d, 0x16e, 0x7, 0x5, 
    0x2, 0x2, 0x16e, 0x16f, 0x5, 0x36, 0x1c, 0x2, 0x16f, 0x170, 0x7, 0x5, 
    0x2, 0x2, 0x170, 0x194, 0x3, 0x2, 0x2, 0x2, 0x171, 0x172, 0x7, 0x4, 
    0x2, 0x2, 0x172, 0x173, 0x7, 0x3c, 0x2, 0x2, 0x173, 0x175, 0x7, 0x4, 
    0x2, 0x2, 0x174, 0x176, 0x5, 0x30, 0x19, 0x2, 0x175, 0x174, 0x3, 0x2, 
    0x2, 0x2, 0x176, 0x177, 0x3, 0x2, 0x2, 0x2, 0x177, 0x175, 0x3, 0x2, 
    0x2, 0x2, 0x177, 0x178, 0x3, 0x2, 0x2, 0x2, 0x178, 0x179, 0x3, 0x2, 
    0x2, 0x2, 0x179, 0x17a, 0x7, 0x5, 0x2, 0x2, 0x17a, 0x17b, 0x5, 0x36, 
    0x1c, 0x2, 0x17b, 0x17c, 0x7, 0x5, 0x2, 0x2, 0x17c, 0x194, 0x3, 0x2, 
    0x2, 0x2, 0x17d, 0x17e, 0x7, 0x4, 0x2, 0x2, 0x17e, 0x17f, 0x7, 0x40, 
    0x2, 0x2, 0x17f, 0x180, 0x5, 0x36, 0x1c, 0x2, 0x180, 0x182, 0x7, 0x4, 
    0x2, 0x2, 0x181, 0x183, 0x5, 0x34, 0x1b, 0x2, 0x182, 0x181, 0x3, 0x2, 
    0x2, 0x2, 0x183, 0x184, 0x3, 0x2, 0x2, 0x2, 0x184, 0x182, 0x3, 0x2, 
    0x2, 0x2, 0x184, 0x185, 0x3, 0x2, 0x2, 0x2, 0x185, 0x186, 0x3, 0x2, 
    0x2, 0x2, 0x186, 0x187, 0x7, 0x5, 0x2, 0x2, 0x187, 0x188, 0x7, 0x5, 
    0x2, 0x2, 0x188, 0x194, 0x3, 0x2, 0x2, 0x2, 0x189, 0x18a, 0x7, 0x4, 
    0x2, 0x2, 0x18a, 0x18b, 0x7, 0x37, 0x2, 0x2, 0x18b, 0x18d, 0x5, 0x36, 
    0x1c, 0x2, 0x18c, 0x18e, 0x5, 0x28, 0x15, 0x2, 0x18d, 0x18c, 0x3, 0x2, 
    0x2, 0x2, 0x18e, 0x18f, 0x3, 0x2, 0x2, 0x2, 0x18f, 0x18d, 0x3, 0x2, 
    0x2, 0x2, 0x18f, 0x190, 0x3, 0x2, 0x2, 0x2, 0x190, 0x191, 0x3, 0x2, 
    0x2, 0x2, 0x191, 0x192, 0x7, 0x5, 0x2, 0x2, 0x192, 0x194, 0x3, 0x2, 
    0x2, 0x2, 0x193, 0x14e, 0x3, 0x2, 0x2, 0x2, 0x193, 0x14f, 0x3, 0x2, 
    0x2, 0x2, 0x193, 0x150, 0x3, 0x2, 0x2, 0x2, 0x193, 0x159, 0x3, 0x2, 
    0x2, 0x2, 0x193, 0x165, 0x3, 0x2, 0x2, 0x2, 0x193, 0x171, 0x3, 0x2, 
    0x2, 0x2, 0x193, 0x17d, 0x3, 0x2, 0x2, 0x2, 0x193, 0x189, 0x3, 0x2, 
    0x2, 0x2, 0x194, 0x37, 0x3, 0x2, 0x2, 0x2, 0x195, 0x196, 0x7, 0x4, 0x2, 
    0x2, 0x196, 0x197, 0x5, 0x24, 0x13, 0x2, 0x197, 0x19b, 0x5, 0x12, 0xa, 
    0x2, 0x198, 0x19a, 0x5, 0x28, 0x15, 0x2, 0x199, 0x198, 0x3, 0x2, 0x2, 
    0x2, 0x19a, 0x19d, 0x3, 0x2, 0x2, 0x2, 0x19b, 0x199, 0x3, 0x2, 0x2, 
    0x2, 0x19b, 0x19c, 0x3, 0x2, 0x2, 0x2, 0x19c, 0x19e, 0x3, 0x2, 0x2, 
    0x2, 0x19d, 0x19b, 0x3, 0x2, 0x2, 0x2, 0x19e, 0x19f, 0x7, 0x5, 0x2, 
    0x2, 0x19f, 0x39, 0x3, 0x2, 0x2, 0x2, 0x1a0, 0x1a1, 0x9, 0x5, 0x2, 0x2, 
    0x1a1, 0x3b, 0x3, 0x2, 0x2, 0x2, 0x1a2, 0x1a3, 0x7, 0x4, 0x2, 0x2, 0x1a3, 
    0x1a4, 0x5, 0x1e, 0x10, 0x2, 0x1a4, 0x1a8, 0x5, 0x2a, 0x16, 0x2, 0x1a5, 
    0x1a7, 0x5, 0x28, 0x15, 0x2, 0x1a6, 0x1a5, 0x3, 0x2, 0x2, 0x2, 0x1a7, 
    0x1aa, 0x3, 0x2, 0x2, 0x2, 0x1a8, 0x1a6, 0x3, 0x2, 0x2, 0x2, 0x1a8, 
    0x1a9, 0x3, 0x2, 0x2, 0x2, 0x1a9, 0x1ab, 0x3, 0x2, 0x2, 0x2, 0x1aa, 
    0x1a8, 0x3, 0x2, 0x2, 0x2, 0x1ab, 0x1ac, 0x7, 0x5, 0x2, 0x2, 0x1ac, 
    0x1c8, 0x3, 0x2, 0x2, 0x2, 0x1ad, 0x1ae, 0x7, 0x4, 0x2, 0x2, 0x1ae, 
    0x1af, 0x5, 0x3a, 0x1e, 0x2, 0x1af, 0x1b3, 0x5, 0x2a, 0x16, 0x2, 0x1b0, 
    0x1b2, 0x5, 0x28, 0x15, 0x2, 0x1b1, 0x1b0, 0x3, 0x2, 0x2, 0x2, 0x1b2, 
    0x1b5, 0x3, 0x2, 0x2, 0x2, 0x1b3, 0x1b1, 0x3, 0x2, 0x2, 0x2, 0x1b3, 
    0x1b4, 0x3, 0x2, 0x2, 0x2, 0x1b4, 0x1b6, 0x3, 0x2, 0x2, 0x2, 0x1b5, 
    0x1b3, 0x3, 0x2, 0x2, 0x2, 0x1b6, 0x1b7, 0x7, 0x5, 0x2, 0x2, 0x1b7, 
    0x1c8, 0x3, 0x2, 0x2, 0x2, 0x1b8, 0x1b9, 0x7, 0x4, 0x2, 0x2, 0x1b9, 
    0x1bb, 0x5, 0x24, 0x13, 0x2, 0x1ba, 0x1bc, 0x5, 0x2a, 0x16, 0x2, 0x1bb, 
    0x1ba, 0x3, 0x2, 0x2, 0x2, 0x1bc, 0x1bd, 0x3, 0x2, 0x2, 0x2, 0x1bd, 
    0x1bb, 0x3, 0x2, 0x2, 0x2, 0x1bd, 0x1be, 0x3, 0x2, 0x2, 0x2, 0x1be, 
    0x1c2, 0x3, 0x2, 0x2, 0x2, 0x1bf, 0x1c1, 0x5, 0x28, 0x15, 0x2, 0x1c0, 
    0x1bf, 0x3, 0x2, 0x2, 0x2, 0x1c1, 0x1c4, 0x3, 0x2, 0x2, 0x2, 0x1c2, 
    0x1c0, 0x3, 0x2, 0x2, 0x2, 0x1c2, 0x1c3, 0x3, 0x2, 0x2, 0x2, 0x1c3, 
    0x1c5, 0x3, 0x2, 0x2, 0x2, 0x1c4, 0x1c2, 0x3, 0x2, 0x2, 0x2, 0x1c5, 
    0x1c6, 0x7, 0x5, 0x2, 0x2, 0x1c6, 0x1c8, 0x3, 0x2, 0x2, 0x2, 0x1c7, 
    0x1a2, 0x3, 0x2, 0x2, 0x2, 0x1c7, 0x1ad, 0x3, 0x2, 0x2, 0x2, 0x1c7, 
    0x1b8, 0x3, 0x2, 0x2, 0x2, 0x1c8, 0x3d, 0x3, 0x2, 0x2, 0x2, 0x1c9, 0x1e4, 
    0x5, 0x3c, 0x1f, 0x2, 0x1ca, 0x1cb, 0x7, 0x4, 0x2, 0x2, 0x1cb, 0x1cc, 
    0x7, 0x42, 0x2, 0x2, 0x1cc, 0x1ce, 0x7, 0x4, 0x2, 0x2, 0x1cd, 0x1cf, 
    0x5, 0x10, 0x9, 0x2, 0x1ce, 0x1cd, 0x3, 0x2, 0x2, 0x2, 0x1cf, 0x1d0, 
    0x3, 0x2, 0x2, 0x2, 0x1d0, 0x1ce, 0x3, 0x2, 0x2, 0x2, 0x1d0, 0x1d1, 
    0x3, 0x2, 0x2, 0x2, 0x1d1, 0x1d2, 0x3, 0x2, 0x2, 0x2, 0x1d2, 0x1d3, 
    0x7, 0x5, 0x2, 0x2, 0x1d3, 0x1d4, 0x7, 0x4, 0x2, 0x2, 0x1d4, 0x1d6, 
    0x5, 0x24, 0x13, 0x2, 0x1d5, 0x1d7, 0x5, 0x2a, 0x16, 0x2, 0x1d6, 0x1d5, 
    0x3, 0x2, 0x2, 0x2, 0x1d7, 0x1d8, 0x3, 0x2, 0x2, 0x2, 0x1d8, 0x1d6, 
    0x3, 0x2, 0x2, 0x2, 0x1d8, 0x1d9, 0x3, 0x2, 0x2, 0x2, 0x1d9, 0x1dd, 
    0x3, 0x2, 0x2, 0x2, 0x1da, 0x1dc, 0x5, 0x28, 0x15, 0x2, 0x1db, 0x1da, 
    0x3, 0x2, 0x2, 0x2, 0x1dc, 0x1df, 0x3, 0x2, 0x2, 0x2, 0x1dd, 0x1db, 
    0x3, 0x2, 0x2, 0x2, 0x1dd, 0x1de, 0x3, 0x2, 0x2, 0x2, 0x1de, 0x1e0, 
    0x3, 0x2, 0x2, 0x2, 0x1df, 0x1dd, 0x3, 0x2, 0x2, 0x2, 0x1e0, 0x1e1, 
    0x7, 0x5, 0x2, 0x2, 0x1e1, 0x1e2, 0x7, 0x5, 0x2, 0x2, 0x1e2, 0x1e4, 
    0x3, 0x2, 0x2, 0x2, 0x1e3, 0x1c9, 0x3, 0x2, 0x2, 0x2, 0x1e3, 0x1ca, 
    0x3, 0x2, 0x2, 0x2, 0x1e4, 0x3f, 0x3, 0x2, 0x2, 0x2, 0x1e5, 0x1e6, 0x7, 
    0x6a, 0x2, 0x2, 0x1e6, 0x1e8, 0x7, 0x4, 0x2, 0x2, 0x1e7, 0x1e9, 0x5, 
    0x38, 0x1d, 0x2, 0x1e8, 0x1e7, 0x3, 0x2, 0x2, 0x2, 0x1e9, 0x1ea, 0x3, 
    0x2, 0x2, 0x2, 0x1ea, 0x1e8, 0x3, 0x2, 0x2, 0x2, 0x1ea, 0x1eb, 0x3, 
    0x2, 0x2, 0x2, 0x1eb, 0x1ec, 0x3, 0x2, 0x2, 0x2, 0x1ec, 0x1ed, 0x7, 
    0x5, 0x2, 0x2, 0x1ed, 0x203, 0x3, 0x2, 0x2, 0x2, 0x1ee, 0x1ef, 0x7, 
    0x52, 0x2, 0x2, 0x1ef, 0x1f1, 0x7, 0x4, 0x2, 0x2, 0x1f0, 0x1f2, 0x5, 
    0x3e, 0x20, 0x2, 0x1f1, 0x1f0, 0x3, 0x2, 0x2, 0x2, 0x1f2, 0x1f3, 0x3, 
    0x2, 0x2, 0x2, 0x1f3, 0x1f1, 0x3, 0x2, 0x2, 0x2, 0x1f3, 0x1f4, 0x3, 
    0x2, 0x2, 0x2, 0x1f4, 0x1f5, 0x3, 0x2, 0x2, 0x2, 0x1f5, 0x1f6, 0x7, 
    0x5, 0x2, 0x2, 0x1f6, 0x203, 0x3, 0x2, 0x2, 0x2, 0x1f7, 0x1f8, 0x7, 
    0x6b, 0x2, 0x2, 0x1f8, 0x203, 0x5, 0x1a, 0xe, 0x2, 0x1f9, 0x1fa, 0x7, 
    0x53, 0x2, 0x2, 0x1fa, 0x203, 0x5, 0x1a, 0xe, 0x2, 0x1fb, 0x1fc, 0x7, 
    0x4e, 0x2, 0x2, 0x1fc, 0x203, 0x5, 0x1a, 0xe, 0x2, 0x1fd, 0x1fe, 0x7, 
    0x6f, 0x2, 0x2, 0x1fe, 0x203, 0x5, 0x1a, 0xe, 0x2, 0x1ff, 0x200, 0x7, 
    0x5b, 0x2, 0x2, 0x200, 0x203, 0x5, 0x1a, 0xe, 0x2, 0x201, 0x203, 0x5, 
    0x28, 0x15, 0x2, 0x202, 0x1e5, 0x3, 0x2, 0x2, 0x2, 0x202, 0x1ee, 0x3, 
    0x2, 0x2, 0x2, 0x202, 0x1f7, 0x3, 0x2, 0x2, 0x2, 0x202, 0x1f9, 0x3, 
    0x2, 0x2, 0x2, 0x202, 0x1fb, 0x3, 0x2, 0x2, 0x2, 0x202, 0x1fd, 0x3, 
    0x2, 0x2, 0x2, 0x202, 0x1ff, 0x3, 0x2, 0x2, 0x2, 0x202, 0x201, 0x3, 
    0x2, 0x2, 0x2, 0x203, 0x41, 0x3, 0x2, 0x2, 0x2, 0x204, 0x205, 0x7, 0x4, 
    0x2, 0x2, 0x205, 0x206, 0x7, 0x14, 0x2, 0x2, 0x206, 0x208, 0x5, 0x10, 
    0x9, 0x2, 0x207, 0x209, 0x5, 0x40, 0x21, 0x2, 0x208, 0x207, 0x3, 0x2, 
    0x2, 0x2, 0x209, 0x20a, 0x3, 0x2, 0x2, 0x2, 0x20a, 0x208, 0x3, 0x2, 
    0x2, 0x2, 0x20a, 0x20b, 0x3, 0x2, 0x2, 0x2, 0x20b, 0x20c, 0x3, 0x2, 
    0x2, 0x2, 0x20c, 0x20d, 0x7, 0x5, 0x2, 0x2, 0x20d, 0x43, 0x3, 0x2, 0x2, 
    0x2, 0x20e, 0x20f, 0x7, 0x6e, 0x2, 0x2, 0x20f, 0x211, 0x7, 0x4, 0x2, 
    0x2, 0x210, 0x212, 0x5, 0x10, 0x9, 0x2, 0x211, 0x210, 0x3, 0x2, 0x2, 
    0x2, 0x212, 0x213, 0x3, 0x2, 0x2, 0x2, 0x213, 0x211, 0x3, 0x2, 0x2, 
    0x2, 0x213, 0x214, 0x3, 0x2, 0x2, 0x2, 0x214, 0x215, 0x3, 0x2, 0x2, 
    0x2, 0x215, 0x216, 0x7, 0x5, 0x2, 0x2, 0x216, 0x221, 0x3, 0x2, 0x2, 
    0x2, 0x217, 0x218, 0x7, 0x56, 0x2, 0x2, 0x218, 0x221, 0x5, 0x1a, 0xe, 
    0x2, 0x219, 0x21a, 0x7, 0x51, 0x2, 0x2, 0x21a, 0x221, 0x5, 0x1a, 0xe, 
    0x2, 0x21b, 0x21c, 0x7, 0x6f, 0x2, 0x2, 0x21c, 0x221, 0x5, 0x1a, 0xe, 
    0x2, 0x21d, 0x21e, 0x7, 0x5b, 0x2, 0x2, 0x21e, 0x221, 0x5, 0x1a, 0xe, 
    0x2, 0x21f, 0x221, 0x5, 0x28, 0x15, 0x2, 0x220, 0x20e, 0x3, 0x2, 0x2, 
    0x2, 0x220, 0x217, 0x3, 0x2, 0x2, 0x2, 0x220, 0x219, 0x3, 0x2, 0x2, 
    0x2, 0x220, 0x21b, 0x3, 0x2, 0x2, 0x2, 0x220, 0x21d, 0x3, 0x2, 0x2, 
    0x2, 0x220, 0x21f, 0x3, 0x2, 0x2, 0x2, 0x221, 0x45, 0x3, 0x2, 0x2, 0x2, 
    0x222, 0x223, 0x7, 0x4, 0x2, 0x2, 0x223, 0x224, 0x7, 0x10, 0x2, 0x2, 
    0x224, 0x226, 0x5, 0x10, 0x9, 0x2, 0x225, 0x227, 0x5, 0x44, 0x23, 0x2, 
    0x226, 0x225, 0x3, 0x2, 0x2, 0x2, 0x227, 0x228, 0x3, 0x2, 0x2, 0x2, 
    0x228, 0x226, 0x3, 0x2, 0x2, 0x2, 0x228, 0x229, 0x3, 0x2, 0x2, 0x2, 
    0x229, 0x22a, 0x3, 0x2, 0x2, 0x2, 0x22a, 0x22b, 0x7, 0x5, 0x2, 0x2, 
    0x22b, 0x47, 0x3, 0x2, 0x2, 0x2, 0x22c, 0x22d, 0x7, 0x4, 0x2, 0x2, 0x22d, 
    0x22e, 0x5, 0x10, 0x9, 0x2, 0x22e, 0x22f, 0x5, 0x12, 0xa, 0x2, 0x22f, 
    0x230, 0x7, 0x5, 0x2, 0x2, 0x230, 0x49, 0x3, 0x2, 0x2, 0x2, 0x231, 0x232, 
    0x7, 0x4, 0x2, 0x2, 0x232, 0x233, 0x5, 0x10, 0x9, 0x2, 0x233, 0x234, 
    0x5, 0x2a, 0x16, 0x2, 0x234, 0x235, 0x7, 0x5, 0x2, 0x2, 0x235, 0x4b, 
    0x3, 0x2, 0x2, 0x2, 0x236, 0x237, 0x7, 0x4, 0x2, 0x2, 0x237, 0x23b, 
    0x5, 0x10, 0x9, 0x2, 0x238, 0x23a, 0x5, 0x4a, 0x26, 0x2, 0x239, 0x238, 
    0x3, 0x2, 0x2, 0x2, 0x23a, 0x23d, 0x3, 0x2, 0x2, 0x2, 0x23b, 0x239, 
    0x3, 0x2, 0x2, 0x2, 0x23b, 0x23c, 0x3, 0x2, 0x2, 0x2, 0x23c, 0x23e, 
    0x3, 0x2, 0x2, 0x2, 0x23d, 0x23b, 0x3, 0x2, 0x2, 0x2, 0x23e, 0x23f, 
    0x7, 0x5, 0x2, 0x2, 0x23f, 0x4d, 0x3, 0x2, 0x2, 0x2, 0x240, 0x242, 0x7, 
    0x4, 0x2, 0x2, 0x241, 0x243, 0x5, 0x4c, 0x27, 0x2, 0x242, 0x241, 0x3, 
    0x2, 0x2, 0x2, 0x243, 0x244, 0x3, 0x2, 0x2, 0x2, 0x244, 0x242, 0x3, 
    0x2, 0x2, 0x2, 0x244, 0x245, 0x3, 0x2, 0x2, 0x2, 0x245, 0x246, 0x3, 
    0x2, 0x2, 0x2, 0x246, 0x247, 0x7, 0x5, 0x2, 0x2, 0x247, 0x25b, 0x3, 
    0x2, 0x2, 0x2, 0x248, 0x249, 0x7, 0x4, 0x2, 0x2, 0x249, 0x24a, 0x7, 
    0x42, 0x2, 0x2, 0x24a, 0x24c, 0x7, 0x4, 0x2, 0x2, 0x24b, 0x24d, 0x5, 
    0x10, 0x9, 0x2, 0x24c, 0x24b, 0x3, 0x2, 0x2, 0x2, 0x24d, 0x24e, 0x3, 
    0x2, 0x2, 0x2, 0x24e, 0x24c, 0x3, 0x2, 0x2, 0x2, 0x24e, 0x24f, 0x3, 
    0x2, 0x2, 0x2, 0x24f, 0x250, 0x3, 0x2, 0x2, 0x2, 0x250, 0x251, 0x7, 
    0x5, 0x2, 0x2, 0x251, 0x253, 0x7, 0x4, 0x2, 0x2, 0x252, 0x254, 0x5, 
    0x4c, 0x27, 0x2, 0x253, 0x252, 0x3, 0x2, 0x2, 0x2, 0x254, 0x255, 0x3, 
    0x2, 0x2, 0x2, 0x255, 0x253, 0x3, 0x2, 0x2, 0x2, 0x255, 0x256, 0x3, 
    0x2, 0x2, 0x2, 0x256, 0x257, 0x3, 0x2, 0x2, 0x2, 0x257, 0x258, 0x7, 
    0x5, 0x2, 0x2, 0x258, 0x259, 0x7, 0x5, 0x2, 0x2, 0x259, 0x25b, 0x3, 
    0x2, 0x2, 0x2, 0x25a, 0x240, 0x3, 0x2, 0x2, 0x2, 0x25a, 0x248, 0x3, 
    0x2, 0x2, 0x2, 0x25b, 0x4f, 0x3, 0x2, 0x2, 0x2, 0x25c, 0x25d, 0x7, 0x4, 
    0x2, 0x2, 0x25d, 0x25e, 0x5, 0x10, 0x9, 0x2, 0x25e, 0x262, 0x7, 0x4, 
    0x2, 0x2, 0x25f, 0x261, 0x5, 0x30, 0x19, 0x2, 0x260, 0x25f, 0x3, 0x2, 
    0x2, 0x2, 0x261, 0x264, 0x3, 0x2, 0x2, 0x2, 0x262, 0x260, 0x3, 0x2, 
    0x2, 0x2, 0x262, 0x263, 0x3, 0x2, 0x2, 0x2, 0x263, 0x265, 0x3, 0x2, 
    0x2, 0x2, 0x264, 0x262, 0x3, 0x2, 0x2, 0x2, 0x265, 0x266, 0x7, 0x5, 
    0x2, 0x2, 0x266, 0x267, 0x5, 0x2a, 0x16, 0x2, 0x267, 0x268, 0x7, 0x5, 
    0x2, 0x2, 0x268, 0x51, 0x3, 0x2, 0x2, 0x2, 0x269, 0x26a, 0x5, 0x10, 
    0x9, 0x2, 0x26a, 0x26e, 0x7, 0x4, 0x2, 0x2, 0x26b, 0x26d, 0x5, 0x30, 
    0x19, 0x2, 0x26c, 0x26b, 0x3, 0x2, 0x2, 0x2, 0x26d, 0x270, 0x3, 0x2, 
    0x2, 0x2, 0x26e, 0x26c, 0x3, 0x2, 0x2, 0x2, 0x26e, 0x26f, 0x3, 0x2, 
    0x2, 0x2, 0x26f, 0x271, 0x3, 0x2, 0x2, 0x2, 0x270, 0x26e, 0x3, 0x2, 
    0x2, 0x2, 0x271, 0x272, 0x7, 0x5, 0x2, 0x2, 0x272, 0x273, 0x5, 0x2a, 
    0x16, 0x2, 0x273, 0x274, 0x5, 0x36, 0x1c, 0x2, 0x274, 0x53, 0x3, 0x2, 
    0x2, 0x2, 0x275, 0x27c, 0x5, 0x10, 0x9, 0x2, 0x276, 0x277, 0x7, 0x4, 
    0x2, 0x2, 0x277, 0x278, 0x7, 0x9, 0x2, 0x2, 0x278, 0x279, 0x5, 0x10, 
    0x9, 0x2, 0x279, 0x27a, 0x7, 0x5, 0x2, 0x2, 0x27a, 0x27c, 0x3, 0x2, 
    0x2, 0x2, 0x27b, 0x275, 0x3, 0x2, 0x2, 0x2, 0x27b, 0x276, 0x3, 0x2, 
    0x2, 0x2, 0x27c, 0x55, 0x3, 0x2, 0x2, 0x2, 0x27d, 0x27f, 0x5, 0x94, 
    0x4b, 0x2, 0x27e, 0x27d, 0x3, 0x2, 0x2, 0x2, 0x27f, 0x282, 0x3, 0x2, 
    0x2, 0x2, 0x280, 0x27e, 0x3, 0x2, 0x2, 0x2, 0x280, 0x281, 0x3, 0x2, 
    0x2, 0x2, 0x281, 0x57, 0x3, 0x2, 0x2, 0x2, 0x282, 0x280, 0x3, 0x2, 0x2, 
    0x2, 0x283, 0x284, 0x7, 0x19, 0x2, 0x2, 0x284, 0x59, 0x3, 0x2, 0x2, 
    0x2, 0x285, 0x286, 0x7, 0x1a, 0x2, 0x2, 0x286, 0x5b, 0x3, 0x2, 0x2, 
    0x2, 0x287, 0x288, 0x7, 0x1b, 0x2, 0x2, 0x288, 0x5d, 0x3, 0x2, 0x2, 
    0x2, 0x289, 0x28a, 0x7, 0x1c, 0x2, 0x2, 0x28a, 0x5f, 0x3, 0x2, 0x2, 
    0x2, 0x28b, 0x28c, 0x7, 0x1d, 0x2, 0x2, 0x28c, 0x61, 0x3, 0x2, 0x2, 
    0x2, 0x28d, 0x28e, 0x7, 0x1e, 0x2, 0x2, 0x28e, 0x63, 0x3, 0x2, 0x2, 
    0x2, 0x28f, 0x290, 0x7, 0x1f, 0x2, 0x2, 0x290, 0x65, 0x3, 0x2, 0x2, 
    0x2, 0x291, 0x292, 0x7, 0x20, 0x2, 0x2, 0x292, 0x67, 0x3, 0x2, 0x2, 
    0x2, 0x293, 0x294, 0x7, 0x21, 0x2, 0x2, 0x294, 0x69, 0x3, 0x2, 0x2, 
    0x2, 0x295, 0x296, 0x7, 0x22, 0x2, 0x2, 0x296, 0x6b, 0x3, 0x2, 0x2, 
    0x2, 0x297, 0x298, 0x7, 0x23, 0x2, 0x2, 0x298, 0x6d, 0x3, 0x2, 0x2, 
    0x2, 0x299, 0x29a, 0x7, 0x24, 0x2, 0x2, 0x29a, 0x6f, 0x3, 0x2, 0x2, 
    0x2, 0x29b, 0x29c, 0x7, 0x25, 0x2, 0x2, 0x29c, 0x71, 0x3, 0x2, 0x2, 
    0x2, 0x29d, 0x29e, 0x7, 0x26, 0x2, 0x2, 0x29e, 0x73, 0x3, 0x2, 0x2, 
    0x2, 0x29f, 0x2a0, 0x7, 0x27, 0x2, 0x2, 0x2a0, 0x75, 0x3, 0x2, 0x2, 
    0x2, 0x2a1, 0x2a2, 0x7, 0x28, 0x2, 0x2, 0x2a2, 0x77, 0x3, 0x2, 0x2, 
    0x2, 0x2a3, 0x2a4, 0x7, 0x29, 0x2, 0x2, 0x2a4, 0x79, 0x3, 0x2, 0x2, 
    0x2, 0x2a5, 0x2a6, 0x7, 0x2a, 0x2, 0x2, 0x2a6, 0x7b, 0x3, 0x2, 0x2, 
    0x2, 0x2a7, 0x2a8, 0x7, 0x2b, 0x2, 0x2, 0x2a8, 0x7d, 0x3, 0x2, 0x2, 
    0x2, 0x2a9, 0x2aa, 0x7, 0x2c, 0x2, 0x2, 0x2aa, 0x7f, 0x3, 0x2, 0x2, 
    0x2, 0x2ab, 0x2ac, 0x7, 0x2d, 0x2, 0x2, 0x2ac, 0x81, 0x3, 0x2, 0x2, 
    0x2, 0x2ad, 0x2ae, 0x7, 0x2e, 0x2, 0x2, 0x2ae, 0x83, 0x3, 0x2, 0x2, 
    0x2, 0x2af, 0x2b0, 0x7, 0x2f, 0x2, 0x2, 0x2b0, 0x85, 0x3, 0x2, 0x2, 
    0x2, 0x2b1, 0x2b2, 0x7, 0x30, 0x2, 0x2, 0x2b2, 0x87, 0x3, 0x2, 0x2, 
    0x2, 0x2b3, 0x2b4, 0x7, 0x31, 0x2, 0x2, 0x2b4, 0x89, 0x3, 0x2, 0x2, 
    0x2, 0x2b5, 0x2b6, 0x7, 0x32, 0x2, 0x2, 0x2b6, 0x8b, 0x3, 0x2, 0x2, 
    0x2, 0x2b7, 0x2b8, 0x7, 0x33, 0x2, 0x2, 0x2b8, 0x8d, 0x3, 0x2, 0x2, 
    0x2, 0x2b9, 0x2ba, 0x7, 0x34, 0x2, 0x2, 0x2ba, 0x8f, 0x3, 0x2, 0x2, 
    0x2, 0x2bb, 0x2bc, 0x7, 0x35, 0x2, 0x2, 0x2bc, 0x91, 0x3, 0x2, 0x2, 
    0x2, 0x2bd, 0x2be, 0x7, 0x36, 0x2, 0x2, 0x2be, 0x93, 0x3, 0x2, 0x2, 
    0x2, 0x2bf, 0x2c0, 0x7, 0x4, 0x2, 0x2, 0x2c0, 0x2c1, 0x5, 0x58, 0x2d, 
    0x2, 0x2c1, 0x2c2, 0x5, 0x36, 0x1c, 0x2, 0x2c2, 0x2c3, 0x7, 0x5, 0x2, 
    0x2, 0x2c3, 0x380, 0x3, 0x2, 0x2, 0x2, 0x2c4, 0x2c5, 0x7, 0x4, 0x2, 
    0x2, 0x2c5, 0x2c6, 0x5, 0x5a, 0x2e, 0x2, 0x2c6, 0x2c7, 0x7, 0x5, 0x2, 
    0x2, 0x2c7, 0x380, 0x3, 0x2, 0x2, 0x2, 0x2c8, 0x2c9, 0x7, 0x4, 0x2, 
    0x2, 0x2c9, 0x2ca, 0x5, 0x5c, 0x2f, 0x2, 0x2ca, 0x2cb, 0x7, 0x5, 0x2, 
    0x2, 0x2cb, 0x380, 0x3, 0x2, 0x2, 0x2, 0x2cc, 0x2cd, 0x7, 0x4, 0x2, 
    0x2, 0x2cd, 0x2ce, 0x5, 0x5e, 0x30, 0x2, 0x2ce, 0x2cf, 0x5, 0x10, 0x9, 
    0x2, 0x2cf, 0x2d0, 0x5, 0x2a, 0x16, 0x2, 0x2d0, 0x2d1, 0x7, 0x5, 0x2, 
    0x2, 0x2d1, 0x380, 0x3, 0x2, 0x2, 0x2, 0x2d2, 0x2d3, 0x7, 0x4, 0x2, 
    0x2, 0x2d3, 0x2d4, 0x5, 0x60, 0x31, 0x2, 0x2d4, 0x2d5, 0x5, 0x10, 0x9, 
    0x2, 0x2d5, 0x2d6, 0x5, 0x4e, 0x28, 0x2, 0x2d6, 0x2d7, 0x7, 0x5, 0x2, 
    0x2, 0x2d7, 0x380, 0x3, 0x2, 0x2, 0x2, 0x2d8, 0x2d9, 0x7, 0x4, 0x2, 
    0x2, 0x2d9, 0x2da, 0x5, 0x62, 0x32, 0x2, 0x2da, 0x2dc, 0x7, 0x4, 0x2, 
    0x2, 0x2db, 0x2dd, 0x5, 0x48, 0x25, 0x2, 0x2dc, 0x2db, 0x3, 0x2, 0x2, 
    0x2, 0x2dd, 0x2de, 0x3, 0x2, 0x2, 0x2, 0x2de, 0x2dc, 0x3, 0x2, 0x2, 
    0x2, 0x2de, 0x2df, 0x3, 0x2, 0x2, 0x2, 0x2df, 0x2e0, 0x3, 0x2, 0x2, 
    0x2, 0x2e0, 0x2e1, 0x7, 0x5, 0x2, 0x2, 0x2e1, 0x2e3, 0x7, 0x4, 0x2, 
    0x2, 0x2e2, 0x2e4, 0x5, 0x4e, 0x28, 0x2, 0x2e3, 0x2e2, 0x3, 0x2, 0x2, 
    0x2, 0x2e4, 0x2e5, 0x3, 0x2, 0x2, 0x2, 0x2e5, 0x2e3, 0x3, 0x2, 0x2, 
    0x2, 0x2e5, 0x2e6, 0x3, 0x2, 0x2, 0x2, 0x2e6, 0x2e7, 0x3, 0x2, 0x2, 
    0x2, 0x2e7, 0x2e8, 0x7, 0x5, 0x2, 0x2, 0x2e8, 0x2e9, 0x7, 0x5, 0x2, 
    0x2, 0x2e9, 0x380, 0x3, 0x2, 0x2, 0x2, 0x2ea, 0x2eb, 0x7, 0x4, 0x2, 
    0x2, 0x2eb, 0x2ec, 0x5, 0x64, 0x33, 0x2, 0x2ec, 0x2ed, 0x5, 0x10, 0x9, 
    0x2, 0x2ed, 0x2f1, 0x7, 0x4, 0x2, 0x2, 0x2ee, 0x2f0, 0x5, 0x2a, 0x16, 
    0x2, 0x2ef, 0x2ee, 0x3, 0x2, 0x2, 0x2, 0x2f0, 0x2f3, 0x3, 0x2, 0x2, 
    0x2, 0x2f1, 0x2ef, 0x3, 0x2, 0x2, 0x2, 0x2f1, 0x2f2, 0x3, 0x2, 0x2, 
    0x2, 0x2f2, 0x2f4, 0x3, 0x2, 0x2, 0x2, 0x2f3, 0x2f1, 0x3, 0x2, 0x2, 
    0x2, 0x2f4, 0x2f5, 0x7, 0x5, 0x2, 0x2, 0x2f5, 0x2f6, 0x5, 0x2a, 0x16, 
    0x2, 0x2f6, 0x2f7, 0x7, 0x5, 0x2, 0x2, 0x2f7, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x2f8, 0x2f9, 0x7, 0x4, 0x2, 0x2, 0x2f9, 0x2fa, 0x5, 0x66, 0x34, 
    0x2, 0x2fa, 0x2fb, 0x5, 0x10, 0x9, 0x2, 0x2fb, 0x2fc, 0x5, 0x12, 0xa, 
    0x2, 0x2fc, 0x2fd, 0x7, 0x5, 0x2, 0x2, 0x2fd, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x2fe, 0x2ff, 0x7, 0x4, 0x2, 0x2, 0x2ff, 0x300, 0x5, 0x68, 0x35, 
    0x2, 0x300, 0x301, 0x5, 0x52, 0x2a, 0x2, 0x301, 0x302, 0x7, 0x5, 0x2, 
    0x2, 0x302, 0x380, 0x3, 0x2, 0x2, 0x2, 0x303, 0x304, 0x7, 0x4, 0x2, 
    0x2, 0x304, 0x305, 0x5, 0x6a, 0x36, 0x2, 0x305, 0x306, 0x5, 0x52, 0x2a, 
    0x2, 0x306, 0x307, 0x7, 0x5, 0x2, 0x2, 0x307, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x308, 0x309, 0x7, 0x4, 0x2, 0x2, 0x309, 0x30a, 0x5, 0x6c, 0x37, 
    0x2, 0x30a, 0x30c, 0x7, 0x4, 0x2, 0x2, 0x30b, 0x30d, 0x5, 0x50, 0x29, 
    0x2, 0x30c, 0x30b, 0x3, 0x2, 0x2, 0x2, 0x30d, 0x30e, 0x3, 0x2, 0x2, 
    0x2, 0x30e, 0x30c, 0x3, 0x2, 0x2, 0x2, 0x30e, 0x30f, 0x3, 0x2, 0x2, 
    0x2, 0x30f, 0x310, 0x3, 0x2, 0x2, 0x2, 0x310, 0x311, 0x7, 0x5, 0x2, 
    0x2, 0x311, 0x313, 0x7, 0x4, 0x2, 0x2, 0x312, 0x314, 0x5, 0x36, 0x1c, 
    0x2, 0x313, 0x312, 0x3, 0x2, 0x2, 0x2, 0x314, 0x315, 0x3, 0x2, 0x2, 
    0x2, 0x315, 0x313, 0x3, 0x2, 0x2, 0x2, 0x315, 0x316, 0x3, 0x2, 0x2, 
    0x2, 0x316, 0x317, 0x3, 0x2, 0x2, 0x2, 0x317, 0x318, 0x7, 0x5, 0x2, 
    0x2, 0x318, 0x319, 0x7, 0x5, 0x2, 0x2, 0x319, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x31a, 0x31b, 0x7, 0x4, 0x2, 0x2, 0x31b, 0x31c, 0x5, 0x6e, 0x38, 
    0x2, 0x31c, 0x31d, 0x5, 0x10, 0x9, 0x2, 0x31d, 0x321, 0x7, 0x4, 0x2, 
    0x2, 0x31e, 0x320, 0x5, 0x10, 0x9, 0x2, 0x31f, 0x31e, 0x3, 0x2, 0x2, 
    0x2, 0x320, 0x323, 0x3, 0x2, 0x2, 0x2, 0x321, 0x31f, 0x3, 0x2, 0x2, 
    0x2, 0x321, 0x322, 0x3, 0x2, 0x2, 0x2, 0x322, 0x324, 0x3, 0x2, 0x2, 
    0x2, 0x323, 0x321, 0x3, 0x2, 0x2, 0x2, 0x324, 0x325, 0x7, 0x5, 0x2, 
    0x2, 0x325, 0x326, 0x5, 0x2a, 0x16, 0x2, 0x326, 0x327, 0x7, 0x5, 0x2, 
    0x2, 0x327, 0x380, 0x3, 0x2, 0x2, 0x2, 0x328, 0x329, 0x7, 0x4, 0x2, 
    0x2, 0x329, 0x32a, 0x5, 0x70, 0x39, 0x2, 0x32a, 0x32b, 0x5, 0x1a, 0xe, 
    0x2, 0x32b, 0x32c, 0x7, 0x5, 0x2, 0x2, 0x32c, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x32d, 0x32e, 0x7, 0x4, 0x2, 0x2, 0x32e, 0x32f, 0x5, 0x72, 0x3a, 
    0x2, 0x32f, 0x330, 0x7, 0x5, 0x2, 0x2, 0x330, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x331, 0x332, 0x7, 0x4, 0x2, 0x2, 0x332, 0x333, 0x5, 0x74, 0x3b, 
    0x2, 0x333, 0x334, 0x7, 0x5, 0x2, 0x2, 0x334, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x335, 0x336, 0x7, 0x4, 0x2, 0x2, 0x336, 0x337, 0x5, 0x76, 0x3c, 
    0x2, 0x337, 0x338, 0x7, 0x5, 0x2, 0x2, 0x338, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x339, 0x33a, 0x7, 0x4, 0x2, 0x2, 0x33a, 0x33b, 0x5, 0x78, 0x3d, 
    0x2, 0x33b, 0x33c, 0x5, 0x9a, 0x4e, 0x2, 0x33c, 0x33d, 0x7, 0x5, 0x2, 
    0x2, 0x33d, 0x380, 0x3, 0x2, 0x2, 0x2, 0x33e, 0x33f, 0x7, 0x4, 0x2, 
    0x2, 0x33f, 0x340, 0x5, 0x7a, 0x3e, 0x2, 0x340, 0x341, 0x7, 0x5, 0x2, 
    0x2, 0x341, 0x380, 0x3, 0x2, 0x2, 0x2, 0x342, 0x343, 0x7, 0x4, 0x2, 
    0x2, 0x343, 0x344, 0x5, 0x7c, 0x3f, 0x2, 0x344, 0x345, 0x5, 0x1c, 0xf, 
    0x2, 0x345, 0x346, 0x7, 0x5, 0x2, 0x2, 0x346, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x347, 0x348, 0x7, 0x4, 0x2, 0x2, 0x348, 0x349, 0x5, 0x7e, 0x40, 
    0x2, 0x349, 0x34a, 0x7, 0x5, 0x2, 0x2, 0x34a, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x34b, 0x34c, 0x7, 0x4, 0x2, 0x2, 0x34c, 0x34d, 0x5, 0x80, 0x41, 
    0x2, 0x34d, 0x34e, 0x7, 0x5, 0x2, 0x2, 0x34e, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x34f, 0x350, 0x7, 0x4, 0x2, 0x2, 0x350, 0x351, 0x5, 0x82, 0x42, 
    0x2, 0x351, 0x352, 0x7, 0x5, 0x2, 0x2, 0x352, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x353, 0x354, 0x7, 0x4, 0x2, 0x2, 0x354, 0x355, 0x5, 0x84, 0x43, 
    0x2, 0x355, 0x357, 0x7, 0x4, 0x2, 0x2, 0x356, 0x358, 0x5, 0x36, 0x1c, 
    0x2, 0x357, 0x356, 0x3, 0x2, 0x2, 0x2, 0x358, 0x359, 0x3, 0x2, 0x2, 
    0x2, 0x359, 0x357, 0x3, 0x2, 0x2, 0x2, 0x359, 0x35a, 0x3, 0x2, 0x2, 
    0x2, 0x35a, 0x35b, 0x3, 0x2, 0x2, 0x2, 0x35b, 0x35c, 0x7, 0x5, 0x2, 
    0x2, 0x35c, 0x35d, 0x7, 0x5, 0x2, 0x2, 0x35d, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x35e, 0x35f, 0x7, 0x4, 0x2, 0x2, 0x35f, 0x360, 0x5, 0x86, 0x44, 
    0x2, 0x360, 0x361, 0x5, 0x12, 0xa, 0x2, 0x361, 0x362, 0x7, 0x5, 0x2, 
    0x2, 0x362, 0x380, 0x3, 0x2, 0x2, 0x2, 0x363, 0x364, 0x7, 0x4, 0x2, 
    0x2, 0x364, 0x365, 0x5, 0x88, 0x45, 0x2, 0x365, 0x366, 0x5, 0x12, 0xa, 
    0x2, 0x366, 0x367, 0x7, 0x5, 0x2, 0x2, 0x367, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x368, 0x369, 0x7, 0x4, 0x2, 0x2, 0x369, 0x36a, 0x5, 0x8a, 0x46, 
    0x2, 0x36a, 0x36b, 0x7, 0x5, 0x2, 0x2, 0x36b, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x36c, 0x36d, 0x7, 0x4, 0x2, 0x2, 0x36d, 0x36e, 0x5, 0x8c, 0x47, 
    0x2, 0x36e, 0x36f, 0x7, 0x5, 0x2, 0x2, 0x36f, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x370, 0x371, 0x7, 0x4, 0x2, 0x2, 0x371, 0x372, 0x5, 0x8e, 0x48, 
    0x2, 0x372, 0x373, 0x5, 0x28, 0x15, 0x2, 0x373, 0x374, 0x7, 0x5, 0x2, 
    0x2, 0x374, 0x380, 0x3, 0x2, 0x2, 0x2, 0x375, 0x376, 0x7, 0x4, 0x2, 
    0x2, 0x376, 0x377, 0x5, 0x90, 0x49, 0x2, 0x377, 0x378, 0x5, 0x10, 0x9, 
    0x2, 0x378, 0x379, 0x7, 0x5, 0x2, 0x2, 0x379, 0x380, 0x3, 0x2, 0x2, 
    0x2, 0x37a, 0x37b, 0x7, 0x4, 0x2, 0x2, 0x37b, 0x37c, 0x5, 0x92, 0x4a, 
    0x2, 0x37c, 0x37d, 0x5, 0x98, 0x4d, 0x2, 0x37d, 0x37e, 0x7, 0x5, 0x2, 
    0x2, 0x37e, 0x380, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x2bf, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x2c4, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x2c8, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x2cc, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x2d2, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x2d8, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x2ea, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x2f8, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x2fe, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x303, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x308, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x31a, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x328, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x32d, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x331, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x335, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x339, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x33e, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x342, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x347, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x34b, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x34f, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x353, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x35e, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x363, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x368, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x36c, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x370, 0x3, 0x2, 0x2, 0x2, 0x37f, 0x375, 0x3, 0x2, 0x2, 
    0x2, 0x37f, 0x37a, 0x3, 0x2, 0x2, 0x2, 0x380, 0x95, 0x3, 0x2, 0x2, 0x2, 
    0x381, 0x382, 0x9, 0x6, 0x2, 0x2, 0x382, 0x97, 0x3, 0x2, 0x2, 0x2, 0x383, 
    0x384, 0x7, 0x4f, 0x2, 0x2, 0x384, 0x3a1, 0x5, 0x1a, 0xe, 0x2, 0x385, 
    0x386, 0x7, 0x54, 0x2, 0x2, 0x386, 0x3a1, 0x5, 0x96, 0x4c, 0x2, 0x387, 
    0x388, 0x7, 0x55, 0x2, 0x2, 0x388, 0x3a1, 0x5, 0x96, 0x4c, 0x2, 0x389, 
    0x38a, 0x7, 0x5d, 0x2, 0x2, 0x38a, 0x3a1, 0x5, 0x96, 0x4c, 0x2, 0x38b, 
    0x38c, 0x7, 0x5e, 0x2, 0x2, 0x38c, 0x3a1, 0x5, 0x96, 0x4c, 0x2, 0x38d, 
    0x38e, 0x7, 0x5f, 0x2, 0x2, 0x38e, 0x3a1, 0x5, 0x96, 0x4c, 0x2, 0x38f, 
    0x390, 0x7, 0x60, 0x2, 0x2, 0x390, 0x3a1, 0x5, 0x96, 0x4c, 0x2, 0x391, 
    0x392, 0x7, 0x61, 0x2, 0x2, 0x392, 0x3a1, 0x5, 0x96, 0x4c, 0x2, 0x393, 
    0x394, 0x7, 0x62, 0x2, 0x2, 0x394, 0x3a1, 0x5, 0x96, 0x4c, 0x2, 0x395, 
    0x396, 0x7, 0x63, 0x2, 0x2, 0x396, 0x3a1, 0x5, 0x96, 0x4c, 0x2, 0x397, 
    0x398, 0x7, 0x64, 0x2, 0x2, 0x398, 0x3a1, 0x5, 0x12, 0xa, 0x2, 0x399, 
    0x39a, 0x7, 0x66, 0x2, 0x2, 0x39a, 0x3a1, 0x5, 0x1a, 0xe, 0x2, 0x39b, 
    0x39c, 0x7, 0x67, 0x2, 0x2, 0x39c, 0x3a1, 0x5, 0x12, 0xa, 0x2, 0x39d, 
    0x39e, 0x7, 0x70, 0x2, 0x2, 0x39e, 0x3a1, 0x5, 0x12, 0xa, 0x2, 0x39f, 
    0x3a1, 0x5, 0x28, 0x15, 0x2, 0x3a0, 0x383, 0x3, 0x2, 0x2, 0x2, 0x3a0, 
    0x385, 0x3, 0x2, 0x2, 0x2, 0x3a0, 0x387, 0x3, 0x2, 0x2, 0x2, 0x3a0, 
    0x389, 0x3, 0x2, 0x2, 0x2, 0x3a0, 0x38b, 0x3, 0x2, 0x2, 0x2, 0x3a0, 
    0x38d, 0x3, 0x2, 0x2, 0x2, 0x3a0, 0x38f, 0x3, 0x2, 0x2, 0x2, 0x3a0, 
    0x391, 0x3, 0x2, 0x2, 0x2, 0x3a0, 0x393, 0x3, 0x2, 0x2, 0x2, 0x3a0, 
    0x395, 0x3, 0x2, 0x2, 0x2, 0x3a0, 0x397, 0x3, 0x2, 0x2, 0x2, 0x3a0, 
    0x399, 0x3, 0x2, 0x2, 0x2, 0x3a0, 0x39b, 0x3, 0x2, 0x2, 0x2, 0x3a0, 
    0x39d, 0x3, 0x2, 0x2, 0x2, 0x3a0, 0x39f, 0x3, 0x2, 0x2, 0x2, 0x3a1, 
    0x99, 0x3, 0x2, 0x2, 0x2, 0x3a2, 0x3ab, 0x7, 0x49, 0x2, 0x2, 0x3a3, 
    0x3ab, 0x7, 0x4a, 0x2, 0x2, 0x3a4, 0x3ab, 0x7, 0x4b, 0x2, 0x2, 0x3a5, 
    0x3ab, 0x7, 0x50, 0x2, 0x2, 0x3a6, 0x3ab, 0x7, 0x5a, 0x2, 0x2, 0x3a7, 
    0x3ab, 0x7, 0x65, 0x2, 0x2, 0x3a8, 0x3ab, 0x7, 0x71, 0x2, 0x2, 0x3a9, 
    0x3ab, 0x5, 0x1c, 0xf, 0x2, 0x3aa, 0x3a2, 0x3, 0x2, 0x2, 0x2, 0x3aa, 
    0x3a3, 0x3, 0x2, 0x2, 0x2, 0x3aa, 0x3a4, 0x3, 0x2, 0x2, 0x2, 0x3aa, 
    0x3a5, 0x3, 0x2, 0x2, 0x2, 0x3aa, 0x3a6, 0x3, 0x2, 0x2, 0x2, 0x3aa, 
    0x3a7, 0x3, 0x2, 0x2, 0x2, 0x3aa, 0x3a8, 0x3, 0x2, 0x2, 0x2, 0x3aa, 
    0x3a9, 0x3, 0x2, 0x2, 0x2, 0x3ab, 0x9b, 0x3, 0x2, 0x2, 0x2, 0x3ac, 0x3ad, 
    0x9, 0x7, 0x2, 0x2, 0x3ad, 0x9d, 0x3, 0x2, 0x2, 0x2, 0x3ae, 0x3b2, 0x7, 
    0x11, 0x2, 0x2, 0x3af, 0x3b2, 0x7, 0xf, 0x2, 0x2, 0x3b0, 0x3b2, 0x5, 
    0x20, 0x11, 0x2, 0x3b1, 0x3ae, 0x3, 0x2, 0x2, 0x2, 0x3b1, 0x3af, 0x3, 
    0x2, 0x2, 0x2, 0x3b1, 0x3b0, 0x3, 0x2, 0x2, 0x2, 0x3b2, 0x9f, 0x3, 0x2, 
    0x2, 0x2, 0x3b3, 0x3b4, 0x7, 0x4, 0x2, 0x2, 0x3b4, 0x3b5, 0x7, 0x21, 
    0x2, 0x2, 0x3b5, 0x3b6, 0x5, 0x52, 0x2a, 0x2, 0x3b6, 0x3b7, 0x7, 0x5, 
    0x2, 0x2, 0x3b7, 0x3d0, 0x3, 0x2, 0x2, 0x2, 0x3b8, 0x3b9, 0x7, 0x4, 
    0x2, 0x2, 0x3b9, 0x3ba, 0x7, 0x22, 0x2, 0x2, 0x3ba, 0x3bb, 0x5, 0x52, 
    0x2a, 0x2, 0x3bb, 0x3bc, 0x7, 0x5, 0x2, 0x2, 0x3bc, 0x3d0, 0x3, 0x2, 
    0x2, 0x2, 0x3bd, 0x3be, 0x7, 0x4, 0x2, 0x2, 0x3be, 0x3bf, 0x7, 0x23, 
    0x2, 0x2, 0x3bf, 0x3c1, 0x7, 0x4, 0x2, 0x2, 0x3c0, 0x3c2, 0x5, 0x50, 
    0x29, 0x2, 0x3c1, 0x3c0, 0x3, 0x2, 0x2, 0x2, 0x3c2, 0x3c3, 0x3, 0x2, 
    0x2, 0x2, 0x3c3, 0x3c1, 0x3, 0x2, 0x2, 0x2, 0x3c3, 0x3c4, 0x3, 0x2, 
    0x2, 0x2, 0x3c4, 0x3c5, 0x3, 0x2, 0x2, 0x2, 0x3c5, 0x3c6, 0x7, 0x5, 
    0x2, 0x2, 0x3c6, 0x3c8, 0x7, 0x4, 0x2, 0x2, 0x3c7, 0x3c9, 0x5, 0x36, 
    0x1c, 0x2, 0x3c8, 0x3c7, 0x3, 0x2, 0x2, 0x2, 0x3c9, 0x3ca, 0x3, 0x2, 
    0x2, 0x2, 0x3ca, 0x3c8, 0x3, 0x2, 0x2, 0x2, 0x3ca, 0x3cb, 0x3, 0x2, 
    0x2, 0x2, 0x3cb, 0x3cc, 0x3, 0x2, 0x2, 0x2, 0x3cc, 0x3cd, 0x7, 0x5, 
    0x2, 0x2, 0x3cd, 0x3ce, 0x7, 0x5, 0x2, 0x2, 0x3ce, 0x3d0, 0x3, 0x2, 
    0x2, 0x2, 0x3cf, 0x3b3, 0x3, 0x2, 0x2, 0x2, 0x3cf, 0x3b8, 0x3, 0x2, 
    0x2, 0x2, 0x3cf, 0x3bd, 0x3, 0x2, 0x2, 0x2, 0x3d0, 0xa1, 0x3, 0x2, 0x2, 
    0x2, 0x3d1, 0x3d2, 0x7, 0x4a, 0x2, 0x2, 0x3d2, 0x3df, 0x5, 0x12, 0xa, 
    0x2, 0x3d3, 0x3d4, 0x7, 0x4b, 0x2, 0x2, 0x3d4, 0x3df, 0x5, 0x1a, 0xe, 
    0x2, 0x3d5, 0x3d6, 0x7, 0x50, 0x2, 0x2, 0x3d6, 0x3df, 0x5, 0x9c, 0x4f, 
    0x2, 0x3d7, 0x3d8, 0x7, 0x5a, 0x2, 0x2, 0x3d8, 0x3df, 0x5, 0x1a, 0xe, 
    0x2, 0x3d9, 0x3da, 0x7, 0x65, 0x2, 0x2, 0x3da, 0x3df, 0x5, 0x9e, 0x50, 
    0x2, 0x3db, 0x3dc, 0x7, 0x71, 0x2, 0x2, 0x3dc, 0x3df, 0x5, 0x1a, 0xe, 
    0x2, 0x3dd, 0x3df, 0x5, 0x28, 0x15, 0x2, 0x3de, 0x3d1, 0x3, 0x2, 0x2, 
    0x2, 0x3de, 0x3d3, 0x3, 0x2, 0x2, 0x2, 0x3de, 0x3d5, 0x3, 0x2, 0x2, 
    0x2, 0x3de, 0x3d7, 0x3, 0x2, 0x2, 0x2, 0x3de, 0x3d9, 0x3, 0x2, 0x2, 
    0x2, 0x3de, 0x3db, 0x3, 0x2, 0x2, 0x2, 0x3de, 0x3dd, 0x3, 0x2, 0x2, 
    0x2, 0x3df, 0xa3, 0x3, 0x2, 0x2, 0x2, 0x3e0, 0x3e1, 0x7, 0x4, 0x2, 0x2, 
    0x3e1, 0x3e2, 0x5, 0x36, 0x1c, 0x2, 0x3e2, 0x3e3, 0x5, 0x36, 0x1c, 0x2, 
    0x3e3, 0x3e4, 0x7, 0x5, 0x2, 0x2, 0x3e4, 0xa5, 0x3, 0x2, 0x2, 0x2, 0x3e5, 
    0x3e6, 0x7, 0x4, 0x2, 0x2, 0x3e6, 0x3e7, 0x5, 0x10, 0x9, 0x2, 0x3e7, 
    0x3e8, 0x5, 0x96, 0x4c, 0x2, 0x3e8, 0x3e9, 0x7, 0x5, 0x2, 0x2, 0x3e9, 
    0xa7, 0x3, 0x2, 0x2, 0x2, 0x3ea, 0x3eb, 0x9, 0x8, 0x2, 0x2, 0x3eb, 0xa9, 
    0x3, 0x2, 0x2, 0x2, 0x3ec, 0x3ed, 0x5, 0x1a, 0xe, 0x2, 0x3ed, 0xab, 
    0x3, 0x2, 0x2, 0x2, 0x3ee, 0x3f2, 0x7, 0x4, 0x2, 0x2, 0x3ef, 0x3f1, 
    0x5, 0x36, 0x1c, 0x2, 0x3f0, 0x3ef, 0x3, 0x2, 0x2, 0x2, 0x3f1, 0x3f4, 
    0x3, 0x2, 0x2, 0x2, 0x3f2, 0x3f0, 0x3, 0x2, 0x2, 0x2, 0x3f2, 0x3f3, 
    0x3, 0x2, 0x2, 0x2, 0x3f3, 0x3f5, 0x3, 0x2, 0x2, 0x2, 0x3f4, 0x3f2, 
    0x3, 0x2, 0x2, 0x2, 0x3f5, 0x3f6, 0x7, 0x5, 0x2, 0x2, 0x3f6, 0xad, 0x3, 
    0x2, 0x2, 0x2, 0x3f7, 0x3fb, 0x7, 0x4, 0x2, 0x2, 0x3f8, 0x3fa, 0x5, 
    0xa6, 0x54, 0x2, 0x3f9, 0x3f8, 0x3, 0x2, 0x2, 0x2, 0x3fa, 0x3fd, 0x3, 
    0x2, 0x2, 0x2, 0x3fb, 0x3f9, 0x3, 0x2, 0x2, 0x2, 0x3fb, 0x3fc, 0x3, 
    0x2, 0x2, 0x2, 0x3fc, 0x3fe, 0x3, 0x2, 0x2, 0x2, 0x3fd, 0x3fb, 0x3, 
    0x2, 0x2, 0x2, 0x3fe, 0x3ff, 0x7, 0x5, 0x2, 0x2, 0x3ff, 0xaf, 0x3, 0x2, 
    0x2, 0x2, 0x400, 0x402, 0x7, 0x4, 0x2, 0x2, 0x401, 0x403, 0x5, 0xa2, 
    0x52, 0x2, 0x402, 0x401, 0x3, 0x2, 0x2, 0x2, 0x403, 0x404, 0x3, 0x2, 
    0x2, 0x2, 0x404, 0x402, 0x3, 0x2, 0x2, 0x2, 0x404, 0x405, 0x3, 0x2, 
    0x2, 0x2, 0x405, 0x406, 0x3, 0x2, 0x2, 0x2, 0x406, 0x407, 0x7, 0x5, 
    0x2, 0x2, 0x407, 0xb1, 0x3, 0x2, 0x2, 0x2, 0x408, 0x40c, 0x7, 0x4, 0x2, 
    0x2, 0x409, 0x40b, 0x5, 0xa0, 0x51, 0x2, 0x40a, 0x409, 0x3, 0x2, 0x2, 
    0x2, 0x40b, 0x40e, 0x3, 0x2, 0x2, 0x2, 0x40c, 0x40a, 0x3, 0x2, 0x2, 
    0x2, 0x40c, 0x40d, 0x3, 0x2, 0x2, 0x2, 0x40d, 0x40f, 0x3, 0x2, 0x2, 
    0x2, 0x40e, 0x40c, 0x3, 0x2, 0x2, 0x2, 0x40f, 0x410, 0x7, 0x5, 0x2, 
    0x2, 0x410, 0xb3, 0x3, 0x2, 0x2, 0x2, 0x411, 0x412, 0x5, 0x26, 0x14, 
    0x2, 0x412, 0xb5, 0x3, 0x2, 0x2, 0x2, 0x413, 0x414, 0x5, 0x20, 0x11, 
    0x2, 0x414, 0xb7, 0x3, 0x2, 0x2, 0x2, 0x415, 0x419, 0x7, 0x4, 0x2, 0x2, 
    0x416, 0x418, 0x5, 0x10, 0x9, 0x2, 0x417, 0x416, 0x3, 0x2, 0x2, 0x2, 
    0x418, 0x41b, 0x3, 0x2, 0x2, 0x2, 0x419, 0x417, 0x3, 0x2, 0x2, 0x2, 
    0x419, 0x41a, 0x3, 0x2, 0x2, 0x2, 0x41a, 0x41c, 0x3, 0x2, 0x2, 0x2, 
    0x41b, 0x419, 0x3, 0x2, 0x2, 0x2, 0x41c, 0x41d, 0x7, 0x5, 0x2, 0x2, 
    0x41d, 0xb9, 0x3, 0x2, 0x2, 0x2, 0x41e, 0x422, 0x7, 0x4, 0x2, 0x2, 0x41f, 
    0x421, 0x5, 0x10, 0x9, 0x2, 0x420, 0x41f, 0x3, 0x2, 0x2, 0x2, 0x421, 
    0x424, 0x3, 0x2, 0x2, 0x2, 0x422, 0x420, 0x3, 0x2, 0x2, 0x2, 0x422, 
    0x423, 0x3, 0x2, 0x2, 0x2, 0x423, 0x425, 0x3, 0x2, 0x2, 0x2, 0x424, 
    0x422, 0x3, 0x2, 0x2, 0x2, 0x425, 0x426, 0x7, 0x5, 0x2, 0x2, 0x426, 
    0xbb, 0x3, 0x2, 0x2, 0x2, 0x427, 0x429, 0x7, 0x4, 0x2, 0x2, 0x428, 0x42a, 
    0x5, 0xa4, 0x53, 0x2, 0x429, 0x428, 0x3, 0x2, 0x2, 0x2, 0x42a, 0x42b, 
    0x3, 0x2, 0x2, 0x2, 0x42b, 0x429, 0x3, 0x2, 0x2, 0x2, 0x42b, 0x42c, 
    0x3, 0x2, 0x2, 0x2, 0x42c, 0x42d, 0x3, 0x2, 0x2, 0x2, 0x42d, 0x42e, 
    0x7, 0x5, 0x2, 0x2, 0x42e, 0xbd, 0x3, 0x2, 0x2, 0x2, 0x42f, 0x43b, 0x5, 
    0xa8, 0x55, 0x2, 0x430, 0x43b, 0x5, 0xaa, 0x56, 0x2, 0x431, 0x43b, 0x5, 
    0xac, 0x57, 0x2, 0x432, 0x43b, 0x5, 0xae, 0x58, 0x2, 0x433, 0x43b, 0x5, 
    0xb0, 0x59, 0x2, 0x434, 0x43b, 0x5, 0xb2, 0x5a, 0x2, 0x435, 0x43b, 0x5, 
    0xb4, 0x5b, 0x2, 0x436, 0x43b, 0x5, 0xb6, 0x5c, 0x2, 0x437, 0x43b, 0x5, 
    0xb8, 0x5d, 0x2, 0x438, 0x43b, 0x5, 0xba, 0x5e, 0x2, 0x439, 0x43b, 0x5, 
    0xbc, 0x5f, 0x2, 0x43a, 0x42f, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x430, 0x3, 
    0x2, 0x2, 0x2, 0x43a, 0x431, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x432, 0x3, 
    0x2, 0x2, 0x2, 0x43a, 0x433, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x434, 0x3, 
    0x2, 0x2, 0x2, 0x43a, 0x435, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x436, 0x3, 
    0x2, 0x2, 0x2, 0x43a, 0x437, 0x3, 0x2, 0x2, 0x2, 0x43a, 0x438, 0x3, 
    0x2, 0x2, 0x2, 0x43a, 0x439, 0x3, 0x2, 0x2, 0x2, 0x43b, 0xbf, 0x3, 0x2, 
    0x2, 0x2, 0x43c, 0x445, 0x7, 0x13, 0x2, 0x2, 0x43d, 0x445, 0x5, 0xbe, 
    0x60, 0x2, 0x43e, 0x445, 0x7, 0x17, 0x2, 0x2, 0x43f, 0x440, 0x7, 0x4, 
    0x2, 0x2, 0x440, 0x441, 0x7, 0xc, 0x2, 0x2, 0x441, 0x442, 0x5, 0x1a, 
    0xe, 0x2, 0x442, 0x443, 0x7, 0x5, 0x2, 0x2, 0x443, 0x445, 0x3, 0x2, 
    0x2, 0x2, 0x444, 0x43c, 0x3, 0x2, 0x2, 0x2, 0x444, 0x43d, 0x3, 0x2, 
    0x2, 0x2, 0x444, 0x43e, 0x3, 0x2, 0x2, 0x2, 0x444, 0x43f, 0x3, 0x2, 
    0x2, 0x2, 0x445, 0xc1, 0x3, 0x2, 0x2, 0x2, 0x4c, 0xcc, 0xd6, 0xe5, 0xec, 
    0xf5, 0xf9, 0xfd, 0x106, 0x10a, 0x112, 0x116, 0x11c, 0x124, 0x128, 0x131, 
    0x143, 0x147, 0x155, 0x15f, 0x16b, 0x177, 0x184, 0x18f, 0x193, 0x19b, 
    0x1a8, 0x1b3, 0x1bd, 0x1c2, 0x1c7, 0x1d0, 0x1d8, 0x1dd, 0x1e3, 0x1ea, 
    0x1f3, 0x202, 0x20a, 0x213, 0x220, 0x228, 0x23b, 0x244, 0x24e, 0x255, 
    0x25a, 0x262, 0x26e, 0x27b, 0x280, 0x2de, 0x2e5, 0x2f1, 0x30e, 0x315, 
    0x321, 0x359, 0x37f, 0x3a0, 0x3aa, 0x3b1, 0x3c3, 0x3ca, 0x3cf, 0x3de, 
    0x3f2, 0x3fb, 0x404, 0x40c, 0x419, 0x422, 0x42b, 0x43a, 0x444, 
  };

  atn::ATNDeserializer deserializer;
  _atn = deserializer.deserialize(_serializedATN);

  size_t count = _atn.getNumberOfDecisions();
  _decisionToDFA.reserve(count);
  for (size_t i = 0; i < count; i++) { 
    _decisionToDFA.emplace_back(_atn.getDecisionState(i), i);
  }
}

SMTLIBv2Parser::Initializer SMTLIBv2Parser::_init;
