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


.PHONY: antlr clean all %.result-z3-test %.result-hylaa-test %.result-hylaa-reduction-test %.result-hylaa-unsat-core-test z3-test shared-clean
test: linear-z3-test linear-hylaa-test linear-hylaa-test linear-hylaa-reduction-test linear-hylaa-unsat-core-test
	$(info testing start)
	@ echo $<

antlr:
	$(info make files for antlr in $(ANTLR_DIR))
	@cd $(ANTLR_DIR)/model && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor
	@cd $(ANTLR_DIR)/config && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 config.g4 -no-listener -visitor

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
	$(info erase experimental results in $(PWD))
	@rm -rf experiment.e* experiment.o*

dev-clean:
	$(info erase unused files in $(ANTLR_DIR))
	@ echo $(linear_src_model)
	@cd $(ANTLR_DIR) && rm -rf model.interp model.tokens modelLexer.* modelParser.py modelVisitor.py
	@cd $(LINEAR_TEST_DIR) && rm -rf *.model_###*

py_include_path := /usr/include/python3.6m
py_lib_path := /usr/lib/python3.6/config-3.6m-x86_64-linux-gnu

wrapper_path := /home/ryu/workspace/STL/src/optimization
test_path := /home/ryu/workspace/STL/src
CC := g++
src_file := $(wildcard $(wrapper_path)/*.cpp)
obj_file := $(wildcard $(wrapper_path)/*.o)

CPPFLAGS := -I$(py_include_path) -I$(wrapper_path) -fPIC
LDFLAGS := -L$(py_lib_path) -L$(wrapper_path)
LIBS := -lstdc++ -lpython3.6m

shared-test := $(src_file:%.cpp=%.o)
shared-gen := $(obj_file:%.o=libtest.so)

shared-library: $(wrapper_path)/libtest.so
test-library: $(test_path)/main.out

$(test_path)/main.out: $(test_path)/main.cpp
	$(CC) $(CPPFLAGS) $(LDFLAGS) -o $(test_path)/main.out $< -ltest $(LIBS)

$(wrapper_path)/%.o: %.cpp
	$(info start testing for 냪)
	$(CC) $< $(LINK)


$(wrapper_path)/libtest.so: $(shared-test)
	@ echo $^
	$(CC) -shared -o $(wrapper_path)/libtest.so $^

shared-clean:
	$(info erase files in $(wrapper_path))
	@cd $(wrapper_path) && rm -rf *.o *.so



# g++  -I/usr/include/python3.6m -I/home/ryu/workspace/STL/src/optimization  -c -o /home/ryu/workspace/STL/src/optimization/wrapper.o /home/ryu/workspace/STL/src/optimization/wrapper.cpp
# g++  -I/usr/include/python3.6m -I/home/ryu/workspace/STL/src/optimization  -c -o /home/ryu/workspace/STL/src/optimization/test.o /home/ryu/workspace/STL/src/optimization/test.cpp

#%.model:
#	@ echo
#	@ echo "Missing model file: $@"
#	@ echo
