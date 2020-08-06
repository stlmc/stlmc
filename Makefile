ANTLR_DIR := $(shell pwd)/stlmcPy/syntax
LINEAR_TEST_DIR := $(shell pwd)/stlmcPy/tests/benchmark_models/linear

#
# All source files in this directory
#
linear_src_model := $(wildcard $(shell pwd)/stlmcPy/tests/benchmark_models/linear/*.model)
linear-z3-test := $(linear_src_model:%.model=%.result-z3)
linear-hylaa-test := $(linear_src_model:%.model=%.result-hylaa)
linear-hylaa-reduction-test := $(linear_src_model:%.model=%.result-hylaa-red)
linear-hylaa-unsat-core-test := $(linear_src_model:%.model=%.result-hylaa-unsat)


.PHONY: antlr clean all %.result-z3-test %.result-hylaa-test %.result-hylaa-reduction-test %.result-hylaa-unsat-core-test z3-test
test: linear-z3-test linear-hylaa-test linear-hylaa-test linear-hylaa-reduction-test linear-hylaa-unsat-core-test
	$(info testing start)
	@ echo $<

antlr:
	$(info make files for antlr in $(ANTLR_DIR))
	@cd $(ANTLR_DIR) && java -jar antlr-4.8-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor

linear-z3-test: $(linear-z3-test)
	@ echo $<

linear-hylaa-test: $(linear-hylaa-test)
	@ echo $<

linear-hylaa-reduction-test: $(linear-hylaa-reduction-test)
	@ echo $<

linear-hylaa-unsat-core-test: $(linear-hylaa-unsat-core-test)
	@ echo $<

%.result-z3: %.model
	$(info start testing for $<)
	@./stlmc $< -l 1 -u 10

%.result-hylaa: %.model
	$(info start testing for $<)
	@./stlmc $< -l 1 -u 10 -solver hylaa

%.result-hylaa-red: %.model
	$(info start testing for $<)
	@./stlmc $< -l 1 -u 10 -solver hylaa-reduction

%.result-hylaa-unsat: %.model
	$(info start testing for $<)
	@./stlmc $< -l 1 -u 10 -solver hylaa-unsat-core


clean:
	$(info erase unused files in $(ANTLR_DIR))
	@ echo $(linear_src_model)
	@cd $(ANTLR_DIR) && rm -rf model.interp model.tokens modelLexer.* modelParser.py modelVisitor.py
	@cd $(LINEAR_TEST_DIR) && rm -rf *.model_###*
#%.model:
#	@ echo
#	@ echo "Missing model file: $@"
#	@ echo