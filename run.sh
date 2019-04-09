rm -r data
#java -jar antlr-4.7.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor 
python3 stlMC_main.py simpleModel/twoThermostatPoly.txt
