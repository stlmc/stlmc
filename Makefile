ANTLR_DIR := $(shell pwd)/stlmcPy/syntax
LINEAR_TEST_DIR := $(shell pwd)/stlmcPy/tests/benchmark_models/linear

#
# All source files in this directory
#
linear_src_model := $(wildcard $(shell pwd)/stlmcPy/tests/benchmark_models/linear/*.model)
linear-test := $(linear_src_model:%.model=%.result)


.PHONY: antlr clean all %.result
all: $(linear-test)
	@ echo $<

antlr:
	$(info make files for antlr in $(ANTLR_DIR))
	@cd $(ANTLR_DIR) && java -jar antlr-4.8-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor

%.result: %.model
	$(info start testing for $<)
	@./stlmc $< -solver hylaa


clean:
	$(info erase unused files in $(ANTLR_DIR))
	@ echo $(linear_src_model)
	@cd $(ANTLR_DIR) && rm -rf model.interp model.tokens modelLexer.* modelParser.py modelVisitor.py

#%.model:
#	@ echo
#	@ echo "Missing model file: $@"
#	@ echo