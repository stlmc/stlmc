ANTLR_DIR=$(shell pwd)/stlmcPy/core/syntax

.PHONY: all clean
all:
	$(info make files for antlr in $(ANTLR_DIR))
	@cd $(ANTLR_DIR) && java -jar antlr-4.8-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor

clean:
	$(info erase unused files in $(ANTLR_DIR))
	@cd $(ANTLR_DIR) && rm -rf model.interp model.tokens modelLexer.* modelParser.py modelVisitor.py