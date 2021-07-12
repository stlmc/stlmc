## Overview

This directory includes the following files:

- supp.pdf: the proof of the lemmas, and the details of the experiments.
- data.zip (1.3MB): the experimental results and log files for the experiments
- INSTALL.md: a file that explains how to install our source code
- stlmc-artifact.ova (3.28GB): a Virtualbox image for the experiments.

---

## Experimental Data of the Paper

The file 'data.zip' contains the following files and directories for the experimental results reported in the paper. For each experiment <EXPR>, the directory '<EXPR>_log' contains the log files generated by running the experiment, and the spreadsheet file '<EXPR>.xlsx' summarizes the results corresponding to the log files.

- data/exp1.xlsx
- data/exp2.xlsx
- data/exp3.xlsx
- data/exp1_log/
- data/exp2_log/
- data/exp3_log/

**(1) RQ1: STL Model Checking of Hybrid Automata**

The spreadsheet file 'exp1.xlsx' contains the following columns for each case of the experiment described in Section VII.A of our paper:

- dynamics: the countinuous dynamics of the model
- model:  the benchmark model
- method:  the model checking algorithm, either New or Old [18]
- formula: the STL formula (1: phi_T^1, 2: phi_T^2, 3: phi_F^1, 4: phi_F^2)
- bound:  a bound n at which each algorithm terminated (or timed out)
- size:   the size of generated SMT encoding for the bound n
- time:   the accumulated execution time up to the bound n
- result:  the result of the STL model checking (TO means a timeout)

Each row of the spreadsheet 'exp1.xlsx' corresponds to an item in Table I and a log file in the directory 'exp1_log'. E.g., the following row of 'exp1.xlsx'

*linear, car, New, 1, 50, 8055, 112.16, TRUE*

corresponds to the case of (Linear, Car, New, phi_T^1) in Table I, and the log file 'exp1_log/linear/car/new/formula1.log'.

**(2) RQ2: Bounded STL Satisfiability Checking**

The spreadsheet file 'exp2.xlsx' contains the following columns for each STL formula considered for the experiment in Section VII.B of our paper:

- model:  the nesting depth of the formula
- method:  the satisfiability encoding method, either New or Old [18]
- formula: the id of the STL formula
- bound:  the smallest bound n for which a satisfying signal is found
- acc size: the accumulated size of the SMT encoding up to the bound n
- time:   the accumulated execution time up to the bound n
- result:  the result of the STL satisfiability checking (TO = a timeout)

Figure 12 in the paper and Table IV in the file 'supp.pdf' are obtained using the spreadsheet file 'exp2.xlsx'. Similarly, each row of the spreadsheet file corresponds to a log file in the directory 'exp2_log'.

**(3) RQ3: Comparison with Reachability Analysis Methods**

The spreadsheet file 'exp3.xlsx' contains the following columns for each case of the experiment described in Section VII.C of our paper:

- dynamics: the countinuous dynamics of the model
- model:  the benchmark model
- method:  the reachability analysis tool/algorithm
- formula: the invariant property (1: I_T, 2: I_F)
- time:   the analysis time 
- result:  the result of the reachability analysis

Similarly, each row of the spreadsheet 'exp3.xlsx' corresponds to an item in Table II and a log file in the directory 'exp3_log'.

---

## Running the Experiments

We will explain how to run each experiment in the paper and how to analyze the results of each execution.

**(1) Experiment 1: STL Model Checking for Hybrid Automata**

As explained in Section VII.A, we consider five hybrid automata models, two variants of continuous dynamics, four STL formulas. See Section B of the file 'supp.pdf' for more details. These models and formulas are declared in the following files (DYNAMICS = linear or poly):

- benchmark/exp1/<DYNAMICS>/car.model
- benchmark/exp1/<DYNAMICS>/therm.model
- benchmark/exp1/<DYNAMICS>/water.model
- benchmark/exp1/<DYNAMICS>/battery.model
- benchmark/exp1/<DYNAMICS>/rail.model

We provide a script to automate the experiments: 'run' in the top directory. The following command run all 80 cases for this experiment (5 models, 2 dynamics, 4 formulas, 2 algorithms) with a 120-minute timeout:

  ~~~
  $ ./run -m exp1 -t 120
  ~~~
  
The argument '-m exp1' denotes the experiment, and '-t 120' denotes a timeout. This command produces a log file subdirectory 'exp1_log' and a spreadsheet report 'exp1.xlsx' in the current directory, explained above.

**(2) Experiment 2: STL Bounded Satisfiability Checking**

In this experiment, we consider 250 STL formulas (50 formulas for each nesting depth 1 <= d <= 5). These formulas are declared in the following files of the form 'nested<DEPTH>.model', where <DEPTH> denotes the nesting depth.

- benchmark/exp2/nested1.model
- benchmark/exp2/nested2.model
- benchmark/exp2/nested3.model
- benchmark/exp2/nested4.model
- benchmark/exp2/nested5.model

Using the script 'run', we can run all 500 cases (250 formulas, two algorithms) with a 30-minute timeout, e.g., by the following command:

  ~~~
  $ ./run -m exp2 -t 30
  ~~~

This command produces a log file subdirectory 'exp2_log' and a spreadsheet report 'exp2.xlsx' in the current directory.

**(3) Experiment 3: Reachability analysis**

In this experiment, we consider the same benchmark models as (1), but written in the input languages of three tools (HyComp, SpaceEx, and Flow*), and two invariant properties (see Section B of 'supp.pdf'). These models are declared in the following files, together with tool-specific files for properties:

- benchmark/exp3/<DYNAMICS>/<TOOL>/reach-car<TOOL-EXT>
- benchmark/exp3/<DYNAMICS>/<TOOL>/reach-therm<TOOL-EXT>
- benchmark/exp3/<DYNAMICS>/<TOOL>/reach-water<TOOL-EXT>
- benchmark/exp3/<DYNAMICS>/<TOOL>/reach-battery<TOOL-EXT>
- benchmark/exp3/<DYNAMICS>/<TOOL>/reach-rail<TOOL-EXT>

with DYNAMICS \in {linear, poly}, TOOL \in {stlmc, hycomp, spaceex, flowstar}, TOOL-EXT \in {.model, _safe.model, _unsafe.model, .hydi, .xml}, where stlmc denotes our algorithms, hydi is a HyComp extension, xml is a SpaceEx extension, and safe/unsafe denotes properties.

The following command runs all cases (in Table II) with a 15-minute timeout:

  ~~~
  $ ./run -m exp3 -t 15
  ~~~

which produces a log file subdirectory 'exp3_log' and a spreadsheet report 'exp3.xlsx' in the current directory.

---

## More Details on Our Script

The 'run' script provides several options to run a subset of the experiments. There are five (optional) command-line arguments as follows:

  ~~~
  $./run -m <MODEL> \ 
	[-t <TIMEOUT>] \
	[-d <DYNAMIC>]\
   	[-alg <ALGORITHM>] \
    	[-tool <TOOL>]
  ~~~

Each option restricts the cases to be executed. Run 'run -h' for more details on the options. The following shows compatible options for each experiment.

| OPTION | MODEL | TIMEOUT | DYNAMIC | ALGORITHM | TOOL |
| :----: | :---: | :-----: | :-----: | :-------: | :--: |
|  RQ1   |   O   |    O    |    O    |     O     |  X   |
|  RQ2   |   O   |    O    |    X    |     O     |  X   |
|  RQ3   |   O   |    O    |    O    |     X     |  O   |

The following shows all available MODEL arguments for each experiment:

- RQ1 : car, therm, water, battery, rail
- RQ2 : nested1, nested2, nested3, nested4, nested5
- RQ3 : reach-car, reach-therm, reach-water, reach-battery, reach-rail 

E.g., the following command runs Experiment RQ1 only for the railroad model with linear dynamics using algorithm New with a timeout of 10 minutes:

	~~~
	$ ./run -m rail -d linear -alg new -t 10
	~~~

The following command runs Experiment RQ2 only for the formulas with nesting depth 2 with a timeout of 5 minutes:
	
	~~~
	$ ./run -m nested2 -alg old -t 5
	~~~

The following command runs Experiment RQ3 only for the railroad model with polynomial dynamics using algorithm ONew with a timeout of 5 minutes:
	
	~~~
	$ ./run -m reach-rail -d poly -tool stlmc-opt -t 5
	~~~
