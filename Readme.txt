We present a new SMT-based model checking algorithm for verifying STL properties of hybrid automata. The algorithm is implemented in the stlMC STL bounded model checker. This artifact includes the model checker and benchmark models including: a number of hybrid automata with different continuous dynamics and STL properties.
To compare the performance of our algorithm with the previous one, we performed the following experiments using such benchmarks:
	(1) STL bounded model checking for hybrid automata
	(2) Bounded satisfiability checking of STL formulas
The experimental results of the paper are obtained by executing the experiments on a 16-core 32-thread Intel Xeon 2.8GHz with 256 GB memory. 
For the TACAS’21 Artifact Evaluation Virtual Machine, please set resources of the machine to "RAM: 2048 MB, number of cores: 1". In this virtual environment, it takes almost 3 times as long as the execution time of the paper.
We provide a way to run an experiment on all benchmark models and a way to run an experiment on only one model.

====================================================

Installation
1. Download stlmc-demo.zip from the link "https://stlmc.github.io/assets/artifact.zip"
2. Unzip stlmc-demo.zip 
	$ unzip stl-demo.zip
3. Go inside the unzipped folder "stl-demo/"
4. Set environments for the artifacts
	$ make && source venv/bin/activate
	$ sudo make install

====================================================

* Experiment 1: STL model checking for Hybrid automata

We perform bounded model checking of STL properties for hybrid automata using our algorithm (new) and the previous algorithm (old) respectively. We consider different step bound (n) and time bounds to different models, since they depending on different model dynamics and parameters. We set a timeout of 180 minutes.
  We consider six hybrid automata models with three variants of continuous dynamics: Linear (L), polynomial of degree 2 (P), and nonlinear-ode (N) dynamics. 
The considered hybrid automata and their dynamics are as follows:
    (1) Thermostat system:          Linear, Polynomial, Nonlinear-ode 
    (2) Watertank system:           Linear, Polynomial, Nonlinear-ode
    (3) Autonomous driving of cars: Linear, Polynomial, Nonlinear-ode
    (4) Railroad gate controllers:  Linear, Polynomial
    (5) Turning an airplain:        Nonlinear-ode
(6) A controller for two batteries: Linear, Polynomial, Nonlinear-ode 
Therefore, five models were considered for each dynamics.
For each model, we consider four STL formulas of different sizes and complexity. 
A hybrid automaton and their STL properties are defined in a model file. In a model file, a hybrid automaton is defined first, and their STL properties are defined after the hybrid automaton. All model files are located in “experiment/exp1” directory corresponding to their dynamics. 
For example, “railroad.model” file that defines the railroad with linear dynamics and their STL properties is located in “experiement/exp1/linear” directory. At the beginning of the file, a hybrid automata of the railroad model are declared and their STL properties are defined from line 82 after the automata declaration.
We perform bounded model checking of STL on the above models to compare the efficiency of our algorithm and the previous one. To perform the model checking, we need some configuration., including: step bounds, time bounds, a solving algorithm (new / old) and a SMT solver (Yices2 / dReal3). 
Parameter values of the paper are generated using “config_gen.py” in the top-level directory. These values can be reset by changing “config_gen.py” and running the configuration file. Please refer to the file for details. We support scripts to execute the experiment with these parameters. Using the script, we can run all models or only one model. 

To execute all benchmark models of the experiment 1, do the following:
	$ ./run -model exp1-all -alg new
	$ ./run -model exp1-all -alg old
We perform the model checking for each STL property of all models at each step bound. Therefore, a total of a thousand cases are executed using the command.

 We can execute only one model at the given step bound, using the following script:
	$ ./run -m <model_name> -d <dynamic> -alg <algorithm> -b <bound>

    Possible arguments for each command option as follows:
	<model_name>:  {thermo, water, car, rail, airplain, battery}
	<dynamic>:     {linear, polynomial, nonlinear-ode}
	<algorithm>:   {new, old}
	<bound> :      Natural number (ex. 1, 2, 3 ….)

 For example, to execute the linear dynamics railroad at “n = 5” using our algorithm, do the following:
	$ ./run -model railroad -d linear -alg new -b 5
We perform the model checking for four STL property of the railroad models at “n=5”. Therefore, total four cases are executed using the command.
 The execution results are related to “Railroad (L /f_1, f_2)” and “Railroad (L /f_3, f_4)” graphs in the Fig. 6 of the paper.

 After the execution, we record the generated formula size, formula generation time, formula solving time, and satisfiability of the STL property for each bound.
For each script, a “<model_algorithm>.csv” file is generated in “data” directory.
The data corresponding to the Fig. 6 of the paper is in “paper_data/exp1” directory. 
To compare the execution results of the railroad with the results of the paper, please see “data/railroad-linear-new.csv” and “paper_data/exp1/linear.csv”.


* Experiment 2: Bounded satisfiability checking of STL formulas

 We perform STL bounded satisfiability checking on STL properties using our algorithm (new) and the previous algorithm (old) respectively, up to step bound n = 20. We set time bounds as 1 for all STL properties, since we don’t need to consider model parameters for the STL satisfiability checking. We use Yices2 for checking the satisfiability. The timeout is 30 minutes.
 We consider 10 STL formulas for each nesting depth d= 1, 2, 3. STL formulas are defined in “nested-i.model” file where i represents the nesting depth. All files are in “experiment/exp2/” directory. 
 For example, “([] (2.35,7.14] ([] [3.62,6.96] p3))“ with nesting depth d = 2 is defined in “experiment/exp2/“nested_2.model”.
We perform satisfiability checking on the above STL formulas to compare the efficiency of our algorithm and the previous one. Similarly, the parameter values used in the paper to perform the satisfaction checking are generated using “config_gen.py”. We can reset the parameter of the experiment 2 by changing the configuration file.
We also support scripts fo experiment 2 that run all models or just one model.

To execute all models of experiment 2, do the following:
	$ ./run -model exp2-all -alg new
	$ ./run -model exp2-all -alg old
We perform the satisfiability checking on all STL properties at each step bound. Therefore, a total of 300 cases are executed using the command.

 We can execute only one model using the following script:
	$ ./run -m <model_name> -alg <algorithm> -b <bound>

    Possible arguments for each command option as follows:
	<model_name>:  {nested-1, nested-2, nested-3}
	<algorithm>:   {new, old}
	<bound>:       Natural number (ex. 1, 2, 3 ….)

 For example, to execute the STL formulas with nesting depth d = 1 at “n = 4” using our algorithm, do the following:
	$ ./run -model nested-1 -alg new -b 4
 The execution results are related to filled boxes of "d(f) = 1" in the Fig. 7 of the paper.

 We save the same information as in the case of the experiment 1 and these information is written at “<nested_i_formula_algorihtm>.csv” file in "data" directory. 
After the execution, we save the same information as in the case of the experiment 1. For each script, a “<model_algorithm>.csv” file is generated in “data” directory.
The data corresponding to the Fig. 7 of the paper is in “paper_data/exp2” directory. 
To compare the execution results of the STL formulas with nesting depth d = 1 and the results of the paper, please see “data/nested-1-new.csv” and “paper_data/exp2/exp2.csv”.



