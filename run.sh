#java -jar antlr-4.7.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor 
python3 ./src/stlMC_main.py ./src/simpleModel/twoThermostatPoly.txt
