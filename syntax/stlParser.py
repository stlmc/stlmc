# Generated from stl.g4 by ANTLR 4.7.1
# encoding: utf-8
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys

def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\26")
        buf.write("D\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\3\2\3\2\3\2\3\2\5\2")
        buf.write("\17\n\2\3\3\3\3\3\3\3\3\3\3\3\3\5\3\27\n\3\3\4\3\4\3\4")
        buf.write("\3\4\3\4\3\4\5\4\37\n\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3")
        buf.write("\5\3\5\3\5\3\5\3\5\3\5\3\5\5\5/\n\5\3\5\3\5\3\5\3\5\3")
        buf.write("\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\7\5?\n\5\f\5\16")
        buf.write("\5B\13\5\3\5\2\3\b\6\2\4\6\b\2\4\3\2\f\r\3\2\n\13\2L\2")
        buf.write("\16\3\2\2\2\4\26\3\2\2\2\6\36\3\2\2\2\b.\3\2\2\2\n\13")
        buf.write("\7\16\2\2\13\17\7\25\2\2\f\r\7\20\2\2\r\17\7\25\2\2\16")
        buf.write("\n\3\2\2\2\16\f\3\2\2\2\17\3\3\2\2\2\20\21\7\25\2\2\21")
        buf.write("\27\7\17\2\2\22\23\7\25\2\2\23\27\7\21\2\2\24\25\7\t\2")
        buf.write("\2\25\27\7\17\2\2\26\20\3\2\2\2\26\22\3\2\2\2\26\24\3")
        buf.write("\2\2\2\27\5\3\2\2\2\30\31\5\2\2\2\31\32\7\22\2\2\32\33")
        buf.write("\5\4\3\2\33\37\3\2\2\2\34\35\7\23\2\2\35\37\7\25\2\2\36")
        buf.write("\30\3\2\2\2\36\34\3\2\2\2\37\7\3\2\2\2 !\b\5\1\2!\"\7")
        buf.write("\3\2\2\"/\5\b\5\f#$\t\2\2\2$%\5\6\4\2%&\5\b\5\13&/\3\2")
        buf.write("\2\2\'(\7\16\2\2()\5\b\5\2)*\7\17\2\2*/\3\2\2\2+/\7\24")
        buf.write("\2\2,/\7\7\2\2-/\7\b\2\2. \3\2\2\2.#\3\2\2\2.\'\3\2\2")
        buf.write("\2.+\3\2\2\2.,\3\2\2\2.-\3\2\2\2/@\3\2\2\2\60\61\f\n\2")
        buf.write("\2\61\62\7\4\2\2\62?\5\b\5\13\63\64\f\t\2\2\64\65\7\5")
        buf.write("\2\2\65?\5\b\5\n\66\67\f\b\2\2\678\t\3\2\289\5\6\4\29")
        buf.write(":\5\b\5\t:?\3\2\2\2;<\f\7\2\2<=\7\6\2\2=?\5\b\5\b>\60")
        buf.write("\3\2\2\2>\63\3\2\2\2>\66\3\2\2\2>;\3\2\2\2?B\3\2\2\2@")
        buf.write(">\3\2\2\2@A\3\2\2\2A\t\3\2\2\2B@\3\2\2\2\b\16\26\36.>")
        buf.write("@")
        return buf.getvalue()


class stlParser ( Parser ):

    grammarFileName = "stl.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'~'", "'/\\'", "'\\/'", "'->'", "'true'", 
                     "'false'", "'inf'", "'U'", "'R'", "'[]'", "'<>'", "'('", 
                     "')'", "'['", "']'", "','", "'='" ]

    symbolicNames = [ "<INVALID>", "NOT", "AND", "OR", "IMP", "TRUE", "FALSE", 
                      "INFTY", "UNTIL", "RELEASE", "GLOBAL", "FINAL", "LPAREN", 
                      "RPAREN", "LBRACK", "RBRACK", "COMMA", "EQUAL", "ID", 
                      "NUMBER", "WS" ]

    RULE_leftEnd = 0
    RULE_rightEnd = 1
    RULE_interval = 2
    RULE_formula = 3

    ruleNames =  [ "leftEnd", "rightEnd", "interval", "formula" ]

    EOF = Token.EOF
    NOT=1
    AND=2
    OR=3
    IMP=4
    TRUE=5
    FALSE=6
    INFTY=7
    UNTIL=8
    RELEASE=9
    GLOBAL=10
    FINAL=11
    LPAREN=12
    RPAREN=13
    LBRACK=14
    RBRACK=15
    COMMA=16
    EQUAL=17
    ID=18
    NUMBER=19
    WS=20

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None



    class LeftEndContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.value = None # Token

        def LPAREN(self):
            return self.getToken(stlParser.LPAREN, 0)

        def NUMBER(self):
            return self.getToken(stlParser.NUMBER, 0)

        def LBRACK(self):
            return self.getToken(stlParser.LBRACK, 0)

        def getRuleIndex(self):
            return stlParser.RULE_leftEnd

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitLeftEnd" ):
                return visitor.visitLeftEnd(self)
            else:
                return visitor.visitChildren(self)




    def leftEnd(self):

        localctx = stlParser.LeftEndContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_leftEnd)
        try:
            self.state = 12
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [stlParser.LPAREN]:
                self.enterOuterAlt(localctx, 1)
                self.state = 8
                self.match(stlParser.LPAREN)
                self.state = 9
                localctx.value = self.match(stlParser.NUMBER)
                pass
            elif token in [stlParser.LBRACK]:
                self.enterOuterAlt(localctx, 2)
                self.state = 10
                self.match(stlParser.LBRACK)
                self.state = 11
                localctx.value = self.match(stlParser.NUMBER)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class RightEndContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.value = None # Token

        def RPAREN(self):
            return self.getToken(stlParser.RPAREN, 0)

        def NUMBER(self):
            return self.getToken(stlParser.NUMBER, 0)

        def RBRACK(self):
            return self.getToken(stlParser.RBRACK, 0)

        def INFTY(self):
            return self.getToken(stlParser.INFTY, 0)

        def getRuleIndex(self):
            return stlParser.RULE_rightEnd

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitRightEnd" ):
                return visitor.visitRightEnd(self)
            else:
                return visitor.visitChildren(self)




    def rightEnd(self):

        localctx = stlParser.RightEndContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_rightEnd)
        try:
            self.state = 20
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,1,self._ctx)
            if la_ == 1:
                self.enterOuterAlt(localctx, 1)
                self.state = 14
                localctx.value = self.match(stlParser.NUMBER)
                self.state = 15
                self.match(stlParser.RPAREN)
                pass

            elif la_ == 2:
                self.enterOuterAlt(localctx, 2)
                self.state = 16
                localctx.value = self.match(stlParser.NUMBER)
                self.state = 17
                self.match(stlParser.RBRACK)
                pass

            elif la_ == 3:
                self.enterOuterAlt(localctx, 3)
                self.state = 18
                localctx.value = self.match(stlParser.INFTY)
                self.state = 19
                self.match(stlParser.RPAREN)
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class IntervalContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def leftEnd(self):
            return self.getTypedRuleContext(stlParser.LeftEndContext,0)


        def COMMA(self):
            return self.getToken(stlParser.COMMA, 0)

        def rightEnd(self):
            return self.getTypedRuleContext(stlParser.RightEndContext,0)


        def EQUAL(self):
            return self.getToken(stlParser.EQUAL, 0)

        def NUMBER(self):
            return self.getToken(stlParser.NUMBER, 0)

        def getRuleIndex(self):
            return stlParser.RULE_interval

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitInterval" ):
                return visitor.visitInterval(self)
            else:
                return visitor.visitChildren(self)




    def interval(self):

        localctx = stlParser.IntervalContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_interval)
        try:
            self.state = 28
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [stlParser.LPAREN, stlParser.LBRACK]:
                self.enterOuterAlt(localctx, 1)
                self.state = 22
                self.leftEnd()
                self.state = 23
                self.match(stlParser.COMMA)
                self.state = 24
                self.rightEnd()
                pass
            elif token in [stlParser.EQUAL]:
                self.enterOuterAlt(localctx, 2)
                self.state = 26
                self.match(stlParser.EQUAL)
                self.state = 27
                self.match(stlParser.NUMBER)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class FormulaContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return stlParser.RULE_formula

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class ParenFormulaContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a stlParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def LPAREN(self):
            return self.getToken(stlParser.LPAREN, 0)
        def formula(self):
            return self.getTypedRuleContext(stlParser.FormulaContext,0)

        def RPAREN(self):
            return self.getToken(stlParser.RPAREN, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitParenFormula" ):
                return visitor.visitParenFormula(self)
            else:
                return visitor.visitChildren(self)


    class ConstantContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a stlParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def TRUE(self):
            return self.getToken(stlParser.TRUE, 0)
        def FALSE(self):
            return self.getToken(stlParser.FALSE, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitConstant" ):
                return visitor.visitConstant(self)
            else:
                return visitor.visitChildren(self)


    class BinaryTemporalFormulaContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a stlParser.FormulaContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(stlParser.FormulaContext)
            else:
                return self.getTypedRuleContext(stlParser.FormulaContext,i)

        def interval(self):
            return self.getTypedRuleContext(stlParser.IntervalContext,0)

        def UNTIL(self):
            return self.getToken(stlParser.UNTIL, 0)
        def RELEASE(self):
            return self.getToken(stlParser.RELEASE, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitBinaryTemporalFormula" ):
                return visitor.visitBinaryTemporalFormula(self)
            else:
                return visitor.visitChildren(self)


    class PropositionContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a stlParser.FormulaContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(stlParser.ID, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitProposition" ):
                return visitor.visitProposition(self)
            else:
                return visitor.visitChildren(self)


    class BinaryFormulaContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a stlParser.FormulaContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def formula(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(stlParser.FormulaContext)
            else:
                return self.getTypedRuleContext(stlParser.FormulaContext,i)

        def AND(self):
            return self.getToken(stlParser.AND, 0)
        def OR(self):
            return self.getToken(stlParser.OR, 0)
        def IMP(self):
            return self.getToken(stlParser.IMP, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitBinaryFormula" ):
                return visitor.visitBinaryFormula(self)
            else:
                return visitor.visitChildren(self)


    class UnaryTemporalFormulaContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a stlParser.FormulaContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def interval(self):
            return self.getTypedRuleContext(stlParser.IntervalContext,0)

        def formula(self):
            return self.getTypedRuleContext(stlParser.FormulaContext,0)

        def GLOBAL(self):
            return self.getToken(stlParser.GLOBAL, 0)
        def FINAL(self):
            return self.getToken(stlParser.FINAL, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitUnaryTemporalFormula" ):
                return visitor.visitUnaryTemporalFormula(self)
            else:
                return visitor.visitChildren(self)


    class UnaryFormulaContext(FormulaContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a stlParser.FormulaContext
            super().__init__(parser)
            self.op = None # Token
            self.copyFrom(ctx)

        def formula(self):
            return self.getTypedRuleContext(stlParser.FormulaContext,0)

        def NOT(self):
            return self.getToken(stlParser.NOT, 0)

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitUnaryFormula" ):
                return visitor.visitUnaryFormula(self)
            else:
                return visitor.visitChildren(self)



    def formula(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = stlParser.FormulaContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 6
        self.enterRecursionRule(localctx, 6, self.RULE_formula, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 44
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [stlParser.NOT]:
                localctx = stlParser.UnaryFormulaContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 31
                localctx.op = self.match(stlParser.NOT)
                self.state = 32
                self.formula(10)
                pass
            elif token in [stlParser.GLOBAL, stlParser.FINAL]:
                localctx = stlParser.UnaryTemporalFormulaContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 33
                localctx.op = self._input.LT(1)
                _la = self._input.LA(1)
                if not(_la==stlParser.GLOBAL or _la==stlParser.FINAL):
                    localctx.op = self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                self.state = 34
                self.interval()
                self.state = 35
                self.formula(9)
                pass
            elif token in [stlParser.LPAREN]:
                localctx = stlParser.ParenFormulaContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 37
                self.match(stlParser.LPAREN)
                self.state = 38
                self.formula(0)
                self.state = 39
                self.match(stlParser.RPAREN)
                pass
            elif token in [stlParser.ID]:
                localctx = stlParser.PropositionContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 41
                self.match(stlParser.ID)
                pass
            elif token in [stlParser.TRUE]:
                localctx = stlParser.ConstantContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 42
                self.match(stlParser.TRUE)
                pass
            elif token in [stlParser.FALSE]:
                localctx = stlParser.ConstantContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 43
                self.match(stlParser.FALSE)
                pass
            else:
                raise NoViableAltException(self)

            self._ctx.stop = self._input.LT(-1)
            self.state = 62
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,5,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 60
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,4,self._ctx)
                    if la_ == 1:
                        localctx = stlParser.BinaryFormulaContext(self, stlParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 46
                        if not self.precpred(self._ctx, 8):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 8)")
                        self.state = 47
                        localctx.op = self.match(stlParser.AND)
                        self.state = 48
                        self.formula(9)
                        pass

                    elif la_ == 2:
                        localctx = stlParser.BinaryFormulaContext(self, stlParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 49
                        if not self.precpred(self._ctx, 7):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 7)")
                        self.state = 50
                        localctx.op = self.match(stlParser.OR)
                        self.state = 51
                        self.formula(8)
                        pass

                    elif la_ == 3:
                        localctx = stlParser.BinaryTemporalFormulaContext(self, stlParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 52
                        if not self.precpred(self._ctx, 6):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 6)")
                        self.state = 53
                        localctx.op = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==stlParser.UNTIL or _la==stlParser.RELEASE):
                            localctx.op = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 54
                        self.interval()
                        self.state = 55
                        self.formula(7)
                        pass

                    elif la_ == 4:
                        localctx = stlParser.BinaryFormulaContext(self, stlParser.FormulaContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_formula)
                        self.state = 57
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 58
                        localctx.op = self.match(stlParser.IMP)
                        self.state = 59
                        self.formula(6)
                        pass

             
                self.state = 64
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,5,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx



    def sempred(self, localctx:RuleContext, ruleIndex:int, predIndex:int):
        if self._predicates == None:
            self._predicates = dict()
        self._predicates[3] = self.formula_sempred
        pred = self._predicates.get(ruleIndex, None)
        if pred is None:
            raise Exception("No predicate with index:" + str(ruleIndex))
        else:
            return pred(localctx, predIndex)

    def formula_sempred(self, localctx:FormulaContext, predIndex:int):
            if predIndex == 0:
                return self.precpred(self._ctx, 8)
         

            if predIndex == 1:
                return self.precpred(self._ctx, 7)
         

            if predIndex == 2:
                return self.precpred(self._ctx, 6)
         

            if predIndex == 3:
                return self.precpred(self._ctx, 5)
         




