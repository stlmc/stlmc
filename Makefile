ANTLR_DIR := $(shell pwd)/src/stlmc/syntax
TEST_DIR := $(shell pwd)/tests
DREAL_DIR := $(shell pwd)/stlmc/3rd_party/dreal
PYTHON ?= python3
FAST ?= 0

DEFAULT_ARTIFACT_SCOPE := .
DEFAULT_ARTIFACT_TIMEOUT := $(if $(filter 1 true yes,$(FAST)),120,3600)
DEFAULT_ARTIFACT_JOBS := $(if $(filter 1 true yes,$(FAST)),4,1)
DEFAULT_ARTIFACT_FAST := $(if $(filter 1 true yes,$(FAST)),--fast,)

.PHONY: all antlr perm clean test test-smoke benchmark

all:    antlr perm

antlr:
	$(info make files for antlr in $(ANTLR_DIR))
	@cd $(ANTLR_DIR)/model && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor
	@cd $(ANTLR_DIR)/config && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 config.g4 -no-listener -visitor
	@cd $(ANTLR_DIR)/visualize && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 visualize.g4 -no-listener -visitor

perm:
	$(info set permission)
	@sudo chmod +x ./scripts/run-exp ./scripts/gen-report ./scripts/gen-table
	@sudo chmod +x $(DREAL_DIR)/dReal $(DREAL_DIR)/dReal-darwin ./stlmc/src/stlmc ./stlmc/src/stlmc-vis

clean:
	$(info erase redundant in $(PWD))
	@cd $(ANTLR_DIR)/model && rm -rf *.interp *.tokens *Lexer* *Parser* *Visitor*
	@cd $(ANTLR_DIR)/config && rm -rf *.interp *.tokens *Lexer* *Parser* *Visitor*
	@cd $(ANTLR_DIR)/visualize && rm -rf *.interp *.tokens *Lexer* *Parser* *Visitor*

test: test-smoke benchmark

test-smoke:
	$(info start SMT solver smoke tests ...)
	@$(PYTHON) $(TEST_DIR)/smoke_solvers.py

benchmark:
	$(info start benchmarks ...)
	@$(PYTHON) $(TEST_DIR)/run_artifact_benchmarks.py \
		$(DEFAULT_ARTIFACT_FAST) \
		--scope $(or $(ARTIFACT_SCOPE),$(DEFAULT_ARTIFACT_SCOPE)) \
		--timeout $(or $(ARTIFACT_TIMEOUT),$(DEFAULT_ARTIFACT_TIMEOUT)) \
		--jobs $(or $(ARTIFACT_JOBS),$(DEFAULT_ARTIFACT_JOBS)) \
		--output $(or $(ARTIFACT_OUTPUT),artifact-logs)
