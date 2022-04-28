ANTLR_DIR := $(shell pwd)/stlmcPy/syntax
SPACEEX_LIB_DIR := $(shell pwd)/stlmcPy/3rd_party/lib

all:    extra-libs antlr spaceex

extra-libs:
	$(info mv libraries)
	@mv ../3rd_party/run ./ && mv ../3rd_party/antlr-4.9.1-complete.jar ./stlmcPy/syntax  && mv ../3rd_party/ ./stlmcPy

antlr:
	$(info make files for antlr in $(ANTLR_DIR))
	@cd $(ANTLR_DIR)/model && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor
	@cd $(ANTLR_DIR)/config && java -jar ../antlr-4.9.1-complete.jar -Dlanguage=Python3 config.g4 -no-listener -visitor

spaceex:
	$(info set spaceex environment)
	@echo 'export LD_LIBRARY_PATH=$$LD_LIBRARY_PATH:'$(SPACEEX_LIB_DIR) >> ~/.bashrc

clean:
	$(info erase redundant in $(PWD))
	@cd $(ANTLR_DIR)/model && rm -rf *.interp *.tokens
	@cd $(ANTLR_DIR)/config && rm -rf *.interp *.tokens
