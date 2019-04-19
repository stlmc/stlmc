CORE_PATH=core/syntax
VILA_PATH=visualize/vila
ORI_PATH=../../
model=$CORE_PATH/model
vila=$VILA_PATH/vila
venv=venv

auto_remove () {
	# remove previous test directories
	# venv: virtual python env
	# always run this script at project root directory
	rm -rf $venv
	rm -rf ${model}.interp ${model}.tokens ${model}Lexer.interp ${model}Lexer.py ${model}Lexer.tokens ${model}Parser.py ${model}Visitor.py
	rm -rf ${vila}.interp ${vila}.tokens ${vila}Lexer.interp ${vila}Lexer.py ${vila}Lexer.tokens ${vila}Parser.py ${vila}Visitor.py
}

install_env () {
	# create and start virtual env
	# setting environment variable
	virtualenv $venv
	. $venv/bin/activate

	# install dependency packages
	pip install -r requirements.txt
}

antlr_setting () {
	cd $CORE_PATH
	# create lexer using antlr 
	# need to install java first if you don't have one
	java -jar antlr-4.7.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor 
	cd $ORI_PATH
}

vila_setting () {
	cd $VILA_PATH
	java -jar antlr-4.7.1-complete.jar -Dlanguage=Python3 vila.g4 -no-listener -visitor
	cd $ORI_PATH
}


case $1 in 
	-rm | --auto-remove ) auto_remove; echo "remove finished"; break;;
	-ai | --auto-install ) install_env; antlr_setting; vila_setting; break;;
	-i | --install ) install_env; echo "install environment finished"; break;;
	-antlr | --antlr-setting ) antlr_setting; echo "antlr setting finished"; break;;
	-vila | --vila-setting ) vila_setting; echo "vila setting finished"; break;;
esac
