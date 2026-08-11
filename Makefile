ANTLR_DIR := $(shell pwd)/src/stlmc/syntax
TEST_DIR := $(shell pwd)/tests
DREAL_DIR := $(shell pwd)/stlmc/3rd_party/dreal
PYTHON ?= python3
FAST ?= 0

DEFAULT_ARTIFACT_SCOPE := .
DEFAULT_ARTIFACT_TIMEOUT := $(if $(filter 1 true yes,$(FAST)),120,3600)
DEFAULT_ARTIFACT_JOBS := $(if $(filter 1 true yes,$(FAST)),4,1)
DEFAULT_ARTIFACT_FAST := $(if $(filter 1 true yes,$(FAST)),--fast,)

.PHONY: all antlr perm clean test test-smoke test-capabilities test-robustness test-reachability test-solver-equivalence benchmark
.NOTPARALLEL: test

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

test: test-smoke test-capabilities test-robustness test-reachability benchmark test-solver-equivalence

test-smoke:
	$(info start SMT solver smoke tests ...)
	@$(PYTHON) -u $(TEST_DIR)/smoke_solvers.py

test-capabilities:
	$(info test solver formula capabilities ...)
	@$(PYTHON) -u $(TEST_DIR)/solver_capabilities.py

test-robustness:
	$(info test STL robustness transformations ...)
	@$(PYTHON) -u $(TEST_DIR)/robustness_operations.py

test-reachability:
	$(info test reachability semantics ...)
	@$(PYTHON) -u $(TEST_DIR)/reachability.py

test-solver-equivalence:
	$(info compare Z3 and Yices results ...)
	@$(PYTHON) -u $(TEST_DIR)/compare_solvers.py \
		$(DEFAULT_ARTIFACT_FAST) \
		--scope $(or $(ARTIFACT_SCOPE),$(DEFAULT_ARTIFACT_SCOPE)) \
		--timeout $(or $(ARTIFACT_TIMEOUT),$(DEFAULT_ARTIFACT_TIMEOUT)) \
		--jobs $(or $(ARTIFACT_JOBS),$(DEFAULT_ARTIFACT_JOBS)) \
		--output $(or $(ARTIFACT_OUTPUT),artifact-logs)

benchmark:
	$(info start benchmarks ...)
	@$(PYTHON) -u $(TEST_DIR)/run_artifact_benchmarks.py \
		$(DEFAULT_ARTIFACT_FAST) \
		--scope $(or $(ARTIFACT_SCOPE),$(DEFAULT_ARTIFACT_SCOPE)) \
		--timeout $(or $(ARTIFACT_TIMEOUT),$(DEFAULT_ARTIFACT_TIMEOUT)) \
		--jobs $(or $(ARTIFACT_JOBS),$(DEFAULT_ARTIFACT_JOBS)) \
		--output $(or $(ARTIFACT_OUTPUT),artifact-logs)
