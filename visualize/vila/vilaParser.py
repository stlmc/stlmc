# Generated from vila.g4 by ANTLR 4.7.1
# encoding: utf-8
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys

def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\f")
        buf.write(".\4\2\t\2\4\3\t\3\4\4\t\4\3\2\3\2\3\2\3\2\5\2\r\n\2\3")
        buf.write("\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\7\2\30\n\2\f\2\16\2")
        buf.write("\33\13\2\3\3\7\3\36\n\3\f\3\16\3!\13\3\3\3\3\3\7\3%\n")
        buf.write("\3\f\3\16\3(\13\3\3\3\3\3\3\4\3\4\3\4\2\3\2\5\2\4\6\2")
        buf.write("\6\3\2\t\n\3\2\6\7\3\2\4\5\3\2\13\f\2\60\2\f\3\2\2\2\4")
        buf.write("\37\3\2\2\2\6+\3\2\2\2\b\t\b\2\1\2\t\n\7\5\2\2\n\r\t\2")
        buf.write("\2\2\13\r\t\2\2\2\f\b\3\2\2\2\f\13\3\2\2\2\r\31\3\2\2")
        buf.write("\2\16\17\f\7\2\2\17\20\7\3\2\2\20\30\5\2\2\b\21\22\f\6")
        buf.write("\2\2\22\23\t\3\2\2\23\30\5\2\2\7\24\25\f\5\2\2\25\26\t")
        buf.write("\4\2\2\26\30\5\2\2\6\27\16\3\2\2\2\27\21\3\2\2\2\27\24")
        buf.write("\3\2\2\2\30\33\3\2\2\2\31\27\3\2\2\2\31\32\3\2\2\2\32")
        buf.write("\3\3\2\2\2\33\31\3\2\2\2\34\36\5\6\4\2\35\34\3\2\2\2\36")
        buf.write("!\3\2\2\2\37\35\3\2\2\2\37 \3\2\2\2 \"\3\2\2\2!\37\3\2")
        buf.write("\2\2\"&\5\2\2\2#%\5\6\4\2$#\3\2\2\2%(\3\2\2\2&$\3\2\2")
        buf.write("\2&\'\3\2\2\2\')\3\2\2\2(&\3\2\2\2)*\7\2\2\3*\5\3\2\2")
        buf.write("\2+,\t\5\2\2,\7\3\2\2\2\7\f\27\31\37&")
        return buf.getvalue()


class vilaParser ( Parser ):

    grammarFileName = "vila.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'='", "'+'", "'-'", "'*'", "'/'" ]

    symbolicNames = [ "<INVALID>", "EQ", "PLUS", "MINUS", "MUL", "DIV", 
                      "WHITEPACE", "NUMBER", "VARIABLE", "COMMENT", "COMMENT_2" ]

    RULE_expression = 0
    RULE_statement = 1
    RULE_comment = 2

    ruleNames =  [ "expression", "statement", "comment" ]

    EOF = Token.EOF
    EQ=1
    PLUS=2
    MINUS=3
    MUL=4
    DIV=5
    WHITEPACE=6
    NUMBER=7
    VARIABLE=8
    COMMENT=9
    COMMENT_2=10

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None



    class ExpressionContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.uniop = None # Token
            self.value = None # Token
            self.operator = None # Token

        def MINUS(self):
            return self.getToken(vilaParser.MINUS, 0)

        def NUMBER(self):
            return self.getToken(vilaParser.NUMBER, 0)

        def VARIABLE(self):
            return self.getToken(vilaParser.VARIABLE, 0)

        def expression(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(vilaParser.ExpressionContext)
            else:
                return self.getTypedRuleContext(vilaParser.ExpressionContext,i)


        def EQ(self):
            return self.getToken(vilaParser.EQ, 0)

        def MUL(self):
            return self.getToken(vilaParser.MUL, 0)

        def DIV(self):
            return self.getToken(vilaParser.DIV, 0)

        def PLUS(self):
            return self.getToken(vilaParser.PLUS, 0)

        def getRuleIndex(self):
            return vilaParser.RULE_expression

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitExpression" ):
                return visitor.visitExpression(self)
            else:
                return visitor.visitChildren(self)



    def expression(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = vilaParser.ExpressionContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 0
        self.enterRecursionRule(localctx, 0, self.RULE_expression, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 10
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [vilaParser.MINUS]:
                self.state = 7
                localctx.uniop = self.match(vilaParser.MINUS)
                self.state = 8
                localctx.value = self._input.LT(1)
                _la = self._input.LA(1)
                if not(_la==vilaParser.NUMBER or _la==vilaParser.VARIABLE):
                    localctx.value = self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                pass
            elif token in [vilaParser.NUMBER, vilaParser.VARIABLE]:
                self.state = 9
                localctx.value = self._input.LT(1)
                _la = self._input.LA(1)
                if not(_la==vilaParser.NUMBER or _la==vilaParser.VARIABLE):
                    localctx.value = self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                pass
            else:
                raise NoViableAltException(self)

            self._ctx.stop = self._input.LT(-1)
            self.state = 23
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,2,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 21
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,1,self._ctx)
                    if la_ == 1:
                        localctx = vilaParser.ExpressionContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expression)
                        self.state = 12
                        if not self.precpred(self._ctx, 5):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 5)")
                        self.state = 13
                        localctx.operator = self.match(vilaParser.EQ)
                        self.state = 14
                        self.expression(6)
                        pass

                    elif la_ == 2:
                        localctx = vilaParser.ExpressionContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expression)
                        self.state = 15
                        if not self.precpred(self._ctx, 4):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 4)")
                        self.state = 16
                        localctx.operator = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==vilaParser.MUL or _la==vilaParser.DIV):
                            localctx.operator = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 17
                        self.expression(5)
                        pass

                    elif la_ == 3:
                        localctx = vilaParser.ExpressionContext(self, _parentctx, _parentState)
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_expression)
                        self.state = 18
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 19
                        localctx.operator = self._input.LT(1)
                        _la = self._input.LA(1)
                        if not(_la==vilaParser.PLUS or _la==vilaParser.MINUS):
                            localctx.operator = self._errHandler.recoverInline(self)
                        else:
                            self._errHandler.reportMatch(self)
                            self.consume()
                        self.state = 20
                        self.expression(4)
                        pass

             
                self.state = 25
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,2,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx

    class StatementContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def expression(self):
            return self.getTypedRuleContext(vilaParser.ExpressionContext,0)


        def EOF(self):
            return self.getToken(vilaParser.EOF, 0)

        def comment(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(vilaParser.CommentContext)
            else:
                return self.getTypedRuleContext(vilaParser.CommentContext,i)


        def getRuleIndex(self):
            return vilaParser.RULE_statement

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitStatement" ):
                return visitor.visitStatement(self)
            else:
                return visitor.visitChildren(self)




    def statement(self):

        localctx = vilaParser.StatementContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_statement)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 29
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==vilaParser.COMMENT or _la==vilaParser.COMMENT_2:
                self.state = 26
                self.comment()
                self.state = 31
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 32
            self.expression(0)
            self.state = 36
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==vilaParser.COMMENT or _la==vilaParser.COMMENT_2:
                self.state = 33
                self.comment()
                self.state = 38
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 39
            self.match(vilaParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class CommentContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def COMMENT(self):
            return self.getToken(vilaParser.COMMENT, 0)

        def COMMENT_2(self):
            return self.getToken(vilaParser.COMMENT_2, 0)

        def getRuleIndex(self):
            return vilaParser.RULE_comment

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitComment" ):
                return visitor.visitComment(self)
            else:
                return visitor.visitChildren(self)




    def comment(self):

        localctx = vilaParser.CommentContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_comment)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 41
            _la = self._input.LA(1)
            if not(_la==vilaParser.COMMENT or _la==vilaParser.COMMENT_2):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx



    def sempred(self, localctx:RuleContext, ruleIndex:int, predIndex:int):
        if self._predicates == None:
            self._predicates = dict()
        self._predicates[0] = self.expression_sempred
        pred = self._predicates.get(ruleIndex, None)
        if pred is None:
            raise Exception("No predicate with index:" + str(ruleIndex))
        else:
            return pred(localctx, predIndex)

    def expression_sempred(self, localctx:ExpressionContext, predIndex:int):
            if predIndex == 0:
                return self.precpred(self._ctx, 5)
         

            if predIndex == 1:
                return self.precpred(self._ctx, 4)
         

            if predIndex == 2:
                return self.precpred(self._ctx, 3)
         




