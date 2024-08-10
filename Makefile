ANTLR_DIR := $(shell pwd)/src/stlmc/syntax
TEST_DIR := $(shell pwd)/tests
DREAL_DIR := $(shell pwd)/stlmc/3rd_party/dreal

all:    antlr perm

antlr:
	$(info make files for antlr in $(ANTLR_DIR))
	@cd $(ANTLR_DIR)/model && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor
	@cd $(ANTLR_DIR)/config && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 config.g4 -no-listener -visitor
	@cd $(ANTLR_DIR)/visualize && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 visualize.g4 -no-listener -visitor

perm:
	$(info set permission)
	@sudo chmod +x ./scripts/run-exp ./scripts/gen-report ./scripts/gen-table
	@sudo chmod +x ./tests/exec $(DREAL_DIR)/dReal $(DREAL_DIR)/dReal-darwin ./stlmc/src/stlmc ./stlmc/src/stlmc-vis

clean:
	$(info erase redundant in $(PWD))
	@cd $(ANTLR_DIR)/model && rm -rf *.interp *.tokens *Lexer* *Parser* *Visitor*
	@cd $(ANTLR_DIR)/config && rm -rf *.interp *.tokens *Lexer* *Parser* *Visitor*
	@cd $(ANTLR_DIR)/visualize && rm -rf *.interp *.tokens *Lexer* *Parser* *Visitor*

test:
	$(info start smoke test ...)
	@exec $(TEST_DIR)/exec
