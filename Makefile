ANTLR_DIR := $(shell pwd)/stlmcPy/syntax

all:	deps antlr

deps:
	$(info install deps)
	@sudo apt update && ./.install

antlr:
	$(info make files for antlr in $(ANTLR_DIR))
	@cd $(ANTLR_DIR)/model && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor
	@cd $(ANTLR_DIR)/config && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 config.g4 -no-listener -visitor

clean:
	$(info erase redundant in $(PWD))
	@cd $(ANTLR_DIR)/model && rm -rf *.interp *.tokens
	@cd $(ANTLR_DIR)/config && rm -rf *.interp *.tokens
