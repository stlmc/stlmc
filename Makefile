TEST_DIR := $(shell pwd)/tests
PYTHON ?= python3
FAST ?= 0

DEFAULT_ARTIFACT_SCOPE := .
DEFAULT_ARTIFACT_TIMEOUT := $(if $(filter 1 true yes,$(FAST)),300,3600)
DEFAULT_ARTIFACT_JOBS := $(if $(filter 1 true yes,$(FAST)),4,1)
DEFAULT_ARTIFACT_FAST := $(if $(filter 1 true yes,$(FAST)),--fast,)

.PHONY: all test test-quick test-parser test-solution-functions test-smoke test-cvc5-solver test-capabilities test-robustness test-temporal-reduction test-scenario-minimization test-cli-help test-install-solvers test-process-cleanup test-reachability test-solver-equivalence test-solver-equivalence-quick benchmark benchmark-quick
.NOTPARALLEL: test

all:
	@echo "Use 'make test' or 'make test-quick' to validate STLmc."

test: test-parser test-solution-functions test-smoke test-cvc5-solver test-capabilities test-robustness test-temporal-reduction test-scenario-minimization test-cli-help test-install-solvers test-process-cleanup test-reachability benchmark test-solver-equivalence

# Short release checks plus benchmark cases that completed within 50 seconds
# in the reference artifact logs. Each selected case gets a 200-second limit.
test-quick: test-parser test-solution-functions test-smoke test-cvc5-solver test-capabilities test-robustness test-temporal-reduction test-scenario-minimization test-cli-help test-install-solvers test-process-cleanup test-reachability benchmark-quick test-solver-equivalence-quick

test-parser:
	$(info test Lark parsers against all input formats ...)
	@$(PYTHON) -u $(TEST_DIR)/parser_inputs.py

test-solution-functions:
	$(info test closed-form solution function semantics ...)
	@$(PYTHON) -u $(TEST_DIR)/solution_functions.py

test-smoke:
	$(info start SMT solver smoke tests ...)
	@$(PYTHON) -u $(TEST_DIR)/smoke_solvers.py

test-cvc5-solver:
	$(info test CVC5 adapter SAT, UNSAT, and assignments ...)
	@$(PYTHON) -u $(TEST_DIR)/cvc5_solver.py

test-capabilities:
	$(info test solver formula capabilities ...)
	@$(PYTHON) -u $(TEST_DIR)/solver_capabilities.py

test-robustness:
	$(info test STL robustness transformations ...)
	@$(PYTHON) -u $(TEST_DIR)/robustness_operations.py

test-temporal-reduction:
	$(info test paper-aligned bounded temporal reduction ...)
	@$(PYTHON) -u $(TEST_DIR)/temporal_reduction.py

test-scenario-minimization:
	$(info test scenario minimization literal polarity ...)
	@$(PYTHON) -u $(TEST_DIR)/scenario_minimization.py

test-cli-help:
	$(info test CLI help coverage ...)
	@$(PYTHON) -u $(TEST_DIR)/cli_help.py

test-install-solvers:
	$(info test solver installer and discovery ...)
	@$(PYTHON) -u $(TEST_DIR)/install_solvers.py

test-process-cleanup:
	$(info test parallel solver process cleanup ...)
	@$(PYTHON) -u $(TEST_DIR)/process_cleanup.py

test-reachability:
	$(info test reachability semantics ...)
	@$(PYTHON) -u $(TEST_DIR)/reachability.py

test-solver-equivalence:
	$(info compare CVC5, Z3, and Yices results ...)
	@$(PYTHON) -u $(TEST_DIR)/compare_solvers.py \
		$(DEFAULT_ARTIFACT_FAST) \
		--scope $(or $(ARTIFACT_SCOPE),$(DEFAULT_ARTIFACT_SCOPE)) \
		--timeout $(or $(ARTIFACT_TIMEOUT),$(DEFAULT_ARTIFACT_TIMEOUT)) \
		--jobs $(or $(ARTIFACT_JOBS),$(DEFAULT_ARTIFACT_JOBS)) \
		--output $(or $(ARTIFACT_OUTPUT),artifact-logs)

test-solver-equivalence-quick:
	$(info compare CVC5, Z3, and Yices on the quick release sample ...)
	@$(PYTHON) -u $(TEST_DIR)/run_artifact_benchmarks.py \
		--scope thm-poly \
		--timeout 120 \
		--jobs 2 \
		--output $(or $(EQUIVALENCE_OUTPUT),artifact-logs-release-equivalence)
	@$(PYTHON) -u $(TEST_DIR)/compare_solvers.py \
		--scope thm-poly \
		--timeout 120 \
		--jobs 2 \
		--output $(or $(EQUIVALENCE_OUTPUT),artifact-logs-release-equivalence)

benchmark:
	$(info start benchmarks ...)
	@$(PYTHON) -u $(TEST_DIR)/run_artifact_benchmarks.py \
		$(DEFAULT_ARTIFACT_FAST) \
		--scope $(or $(SCOPE),$(ARTIFACT_SCOPE),$(DEFAULT_ARTIFACT_SCOPE)) \
		$(if $(MODEL),--model "$(MODEL)") \
		$(if $(FORMULA),--formula "$(FORMULA)") \
		$(if $(BATCH),--solver-batch-size "$(BATCH)") \
		--timeout $(or $(TIMEOUT),$(ARTIFACT_TIMEOUT),$(DEFAULT_ARTIFACT_TIMEOUT)) \
		--jobs $(or $(ARTIFACT_JOBS),$(DEFAULT_ARTIFACT_JOBS)) \
		--output $(or $(OUTPUT),$(ARTIFACT_OUTPUT),artifact-logs)

benchmark-quick:
	$(info start quick release benchmarks ...)
	@$(PYTHON) -u $(TEST_DIR)/run_artifact_benchmarks.py \
		--quick \
		--timeout 200 \
		--jobs $(or $(QUICK_JOBS),4) \
		--output $(or $(QUICK_OUTPUT),$(ARTIFACT_OUTPUT),artifact-logs)
