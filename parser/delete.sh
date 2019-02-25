rm *.tokens
rm *.interp
rm modelLexer.*
rm modelParser.*
java -jar antlr-4.7.1-complete.jar -Dlanguage=Python3 model.g4 -no-listener -visitor 
python3 stlMC_main.py ../simpleModel/simple.txt

