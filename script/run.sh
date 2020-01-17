#!/bin/bash

CORE_PATH=../stlmcPy/core/syntax
model=../src/$CORE_PATH/model
PY_DIR=../src
TEST_DIR=../src/simpleModel
venv=../src/venv
node_dir=../visualize
go_dir=../visualize/golang

auto_remove () {
	# remove previous test directories
	# venv: virtual python env
	# always run this script at project root directory
	rm -rf $venv
	rm -rf ${model}.interp ${model}.tokens ${model}Lexer.interp ${model}Lexer.py ${model}Lexer.tokens ${model}Parser.py ${model}Visitor.py
	rm -rf $PY_DIR/*.smt2
	rm -rf $go_dir/main
}

install_env () {
	# create and start virtual env
	# setting environment variable
	virtualenv $venv
	. $venv/bin/activate

	# install dependency packages
	pip install -r $PY_DIR/requirements.txt
	rm -f $PY_DIR/*.smt2
}

antlr_setting () {
	cd $CORE_PATH
	# create lexer using antlr 
	# need to install java first if you don't have one
	java -jar antlr-4.7.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor 
}

runModel () {
    #python3 stlMC_main.py simpleModel/twoThermostatPoly.txt
    #python3 stlMC_main.py simpleModel/twoBatteryPoly.txt
    #python3 stlMC_main.py simpleModel/twoBatteryLinear.txt
    #python3 stlMC_main.py simpleModel/twoWatertankLinear.txt
    #python3 stlMC_main.py simpleModel/railroadPoly.txt
    #python3 stlMC_main.py simpleModel/twoCarPoly.txt
    #python3 stlMC_main.py simpleModel/twoWatertankPoly.txt
    if [ -z "$1" ]
    then
        echo "no arg"
        echo "Default simpleModel will be run."
        echo "Usage: \n\t ./run --run some_file"
        if [ -f $TEST_DIR/"twoThermostatPoly.txt" ]
        then
            python3 $PY_DIR/stlMC_main.py $TEST_DIR/"twoThermostatPoly.txt"
        else
            echo "twoThermostatPoly.txt not found!"
        fi
    else
        if [ -f $TEST_DIR/$1".txt" ]
        then
            python3 $PY_DIR/stlMC_main.py $TEST_DIR/$1".txt"
        else
            echo "No such file"
        fi
    fi
    rm -f *.smt2
}

build_all(){
    cd $node_dir
    npm install
    npm run build

    cd golang
    go build main.go
}

case $1 in 
	-rm | --auto-remove ) auto_remove; echo "remove finished";;
  -build ) build_all; echo "build finished";;
	-i | --auto-install ) install_env; antlr_setting;;
	-ie | --install-env ) install_env; echo "install environment finished";;
	--run ) runModel "$2"; echo "run finished";;
	-antlr | --antlr-setting ) antlr_setting; echo "antlr setting finished";;
esac
