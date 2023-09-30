This file explains the artifact for our paper "STLmc: Robust STL Model Checking
of Hybrid Systems using SMT". 

The STLmc tool is available on our tool webpage:

 https://stlmc.github.io/




======================================================
1. Artifact Overview
======================================================


In this section, we explain the overview of our STLmc tool artifact. The artifact includes 
the following things: 

  (1) a short demo of the STLmc tool,
  (2) a script to run the experiments in the paper, and
  (3) additional examples providing more detailed usages not included in the paper.

Part (1) explains how to execute the input model and visualize counterexamples 
in Section 3 of the paper. Part (2) shows how to reproduce the experimental results 
in Table 2 in Section 5 of the paper. Part (3) describes an additional demo and 
additional benchmark models not included in the paper for the 'reusable' badge.

The STLmc artifact includes the following files and directories:

- AUTHORS.md : authors information,
- LICENSE.md : the STLmc tool license,
- Makefile : a makefile for generating Antlr4 parser and setting permissions for executables,
- benchmarks : benchmark models for our paper and additional experiments,
- scripts: experiment reproduction scripts,
- stlmc : the source codes and executables of STLmc,
- paper.pdf : an accepted paper,
- logs : the experimental results and raw log files of the experiments that run on provided VM.

The rest of 'README' is organized as follows. Section 2 provides how to set up the artifact using 
a virtual box image. Section 3 explains rudimentary testing. Section 4 describes a short demo of 
the STLmc tool in Section 3 of the paper. Section 5 explains how to reproduce the experiments in 
Section 5 of the paper. Section 6 explains the structure of the log files for the experiments. 
Section 7 explains the most relevant parts of the source code. Section 8 explains the structure 
of the benchmark model directories. Section 9 provides additional examples of various options 
not used in the paper. Section 10 explains how to run additional experiments and more details 
on our scripts. Section 11 explains supplemental materials. Finally, Section 12 provides guidance 
on how to run the artifact without VM. 

For the 'functional' badge, we provide rudimentary testing, scripts to reproduce the results 
of the paper, log files, and explanations of the interesting parts of the source code.
These are explained in Sections 2 through 7. For the 'reusable' badge, we explain more 
usages of the STLmc tool, additional experiments, and instructions for installing the artifact 
without a VM image. These are explained in Sections 8 through 12.


 

======================================================
2. Running the VirtualBox Image
======================================================


We provide a URL for the VM image 'STLmc.ova' via our tool webpage:

  https://stlmc.github.io/cav2022-artifact

This VM image contains our tool and experiments (with Ubuntu 18.04.6 installed). The size 
of the image is about 4GB. A minimum system requirement is a quad-core machine with 
4GB memory. You can run the image using VirtualBox (https://www.virtualbox.org) as follows:

- Download 'STLmc.ova' from our webpage (https://stlmc.github.io/cav2022-artifact)
- Click 'File/Import Appliance' in the top menu.
- Choose 'STLmc.ova', and click 'Continue'.
- Set the number of CPU cores (>= 4) and the size of memory (>= 4GB).
- Click 'Import' (which will take a few minutes).
- Click the green right arrow to run the imported image.

Remark: Some experiments may not run properly on the following architectures:
- Apple MacBook Pro 2015 or earlier: Yices 2.6 with QF-NRA is not working




======================================================
3. Rudimentary Testing
======================================================


We provide rudimentary testing to check there are no problems running the STLmc tool.
The tests check whether the prerequisites, such as Python 3, Yices, dReal, etc., 
are installed well and run the STLmc tool using simple models.

The following command runs the tests: 
  
user@VB:~/CAV2022-AeC$ make test

If the tests succeed, you will see the following messages:

  start smoke test ...
  [exec] Python: pass
  [exec] Yices: pass
  [exec] dReal: pass
  [exec] Z3: pass
  [exec] Java: pass
  [exec] Gnuplot: pass
  [file] Config: pass
  [smt] dReal
    ./tests/smt2/dreal/01.smt2: pass
    ./tests/smt2/dreal/02.smt2: pass
  [smt] Z3
    ./tests/smt2/z3/01.smt2: pass
    ./tests/smt2/z3/02.smt2: pass
  [smt] Yices
    ./tests/smt2/yices2/01.smt2: pass
    ./tests/smt2/yices2/02.smt2: pass
  [tool] STLmc
    ./tests/stlmc/01.model: pass
    ./tests/stlmc/02.model: pass




======================================================
4. Short Demo of the STLmc Tool
======================================================


In this section, we shortly demonstrate the usage of the STLmc tool on our VM (i.e., STLmc.ova)
using the two networked thermostat controller model, explained in Sec. 3 of our paper.

To start the STLmc tool, go to the 'stlmc/src' directory of the artifact: 

user@VB:~$ cd '/home/user/CAV2022-AeC/stlmc/src' 

We can use the script 'stlmc' in the 'stlmc/src' directory to start the STLmc tool. The following 
command finds a counterexample of the formula 'f2' of the thermostat model at bound 2 
with respect to robustness threshold 2 using parallelized 2-step algorithm and dReal:

user@VB:~/CAV2022-AeC/stlmc/src$./stlmc ../../benchmarks/paper/thm-ode/therm.model -bound 5 -time-bound 30 -threshold 2 -goal f2 -solver dreal -two-step -parallel -visualize

The analysis in VM took 91 seconds on AMD Ryzen 9 3.3GHz with quad-core and 4GB of memory. 

When the '-visualize' option is set and there is a counterexample, the STLmc tool 
creates a counterexample file and a visualization configuration file to draw graphs 
for the counterexample. The configuration file contains information about variables 
to draw, the storage format of the graph, and grouping information to draw into one graph. 

The above command generates a counterexample file, named 'therm_b5_f2_dreal.counterexample', 
and a visualization configuration file, named 'therm_b5_f2_dreal.cfg', in the current directory.
The contents of 'therm_b5_f2_dreal.cfg' are as follows:

{
# state variables: x0 , x1
# f2_0 ---> ([][2.0,4.0] (((x0 - x1) >= 4) -> (<>[3.0,10.0] ((x0 - x1) <= -3))))
# f2_1 ---> (((x0 - x1) >= 4) -> (<>[3.0,10.0] ((x0 - x1) <= -3)))
# f2_2 ---> (not ((x0 - x1) >= 4))
# f2_3 ---> (<>[3.0,10.0] ((x0 - x1) <= -3))
# f2_4 ---> ((x0 - x1) >= 4)
# f2_5 ---> ((x0 - x1) <= -3)
output = html # pdf
group {
}
}

The STLmc tool provides the script 'stlmc-vis' to draw counterexample signals and robustness degrees. 
For example, the counterexample graphs for the property 'f2' of the thermostat can be generated 
using the following command:

user@VB:~/CAV2022-AeC/stlmc/src$./stlmc-vis therm_b5_f2_dreal.counterexample

The default visualization configuration creates two graphs: (1) a graph for continuous state
variables and (2) a graph for robustness degrees of STL subformulas. The grouping information 
to draw into one graph can be changed by modifying the visualization configuration file. 
Variables in the same group are displayed on the same graph. 

For example, we can generate four graphs corresponding to Figure 3 of our paper 
by modifying the group attributes in 'therm_b5_f2_dreal.cfg' as follows:
  
{ 
# state variables: x0 , x1
# f2_1 ---> (((x0 - x1) >= 4) -> (<>[3.0,10.0] ((x0 - x1) <= -3)))
# f2_0 ---> ([][2.0,4.0] (((x0 - x1) >= 4) -> (<>[3.0,10.0] ((x0 - x1) <= -3))))
# f2_4 ---> ((x0 - x1) >= 4)
# f2_2 ---> (not ((x0 - x1) >= 4))
# f2_3 ---> (<>[3.0,10.0] ((x0 - x1) <= -3))
# f2_5 ---> ((x0 - x1) <= -3)
output = html # pdf
group {
 (x0, x1), (f2_0, f2_1), (f2_2, f2_3), (f2_4, f2_5)
}
}
    
These four graphs can be viewed in 'therm_b5_f2_dreal.counterexample.html' created by rerunning 
the following command:

user@VB:~/CAV2022-AeC/stlmc/src$./stlmc-vis therm_b5_f2_dreal.counterexample




======================================================
5. Running the Experiments 
======================================================


In this section, we explain how to reproduce the experiment of the paper in Section 5 
In Section 5 of our paper, we evaluate the effectiveness of the STLmc tool using a number of
hybrid system benchmarks and nontrivial STL properties. We consider a total of 18 cases 
as indicated in Table 2 of our paper, taking into account six benchmark models and 
three STL formulas for each model.

We provide the script 'run_exp' in the 'scripts' subdirectory to automate the experiments. 
The models of the experiments are located in the 'benchmarks/paper' subdirectory.
The following command run all these models (6 models, 3 formulas):

user@VB:~/CAV2022-AeC/scripts$ ./run-exp ../benchmarks/paper/ -t 1800

The command-line argument '-t 1800' denotes a 1800-second timeout. This command creates a 'log' 
subdirectory in the current directory. The log files for each case are in the 'log' subdirectory.

The above command in VM took about 1 hour on AMD Ryzen 9 3.3GHz with quad-core and 4GB of memory. 

We provide the script 'gen-table' to generate a table summarizing results in the format of Table 2 
in our paper. The script 'gen-table' uses the log files located in the 'log' subdirectory to generate 
the table. For example, the following command generates the file 'log-table.html' corresponding to
Table 2 of the paper in the same directory:

user@VB:~/CAV2022-AeC/scripts$ ./gen-table




======================================================
6. Log Files for the Experiments
======================================================


The subdirectory 'logs' of the top artifact directory 'CAV2022-AeC' contains the log files, 
CSV reports, and html tables for the experiments. There are two subdirectories in the 'logs': 
(1) non-vm, and (2) vm. In the 'logs/non-vm' subdirectory, there are experimental results that 
were run in the same environment as the paper (Intel Xeon 2.8GHz with 256GB memory). In the 
'logs/vm' subdirectory, there are experimental results that were run in VM on AMD Ryzen 9 3.3GHz 
with quad-core and 4GB of memory. 

The results of the experiment of the paper are placed in the 'paper' subdirectory and 
the results of the additional experiment are placed in the 'additional' subdirectory. 
These results are placed in the following directory, where <ENV> is one of {'non-vm', 'vm'} 
and <N> is one of {1, 2, 3, 4, 5}:

- logs/<ENV>/paper/trial-<N>.zip: a zip file of the log files of N-th trial of the experiment of the paper in Section 5
- logs/<ENV>/paper/trial-<N>-report.csv: a CSV report of the N-th trial log files
- logs/<ENV>/paper/trial-<N>-table.html: an html table corresponding to Table 2 of our paper 

- logs/<ENV>/additional/raw.zip: a zip file of the log files of the extended experiments of the technical report in Section 5
- logs/<ENV>/additional/raw-report.csv: a CSV report of raw.zip
- logs/<ENV>/additional/raw-table.html: the html table corresponding to Table 2 and Table 3 of the technical report

Note that due to concurrency and non-determinism of parallelization algorithm, 
the bound (k) at which a counterexample is found may differ by up to '1'. 
Thus, we run five times for the reproduction of the experiment of the paper.




======================================================
7. Interesting Parts of STLmc Source Code
======================================================


The full source code of our tool is located in the 'stlmc/src' subdirectory of the top directory 
'CAV2022-AeC'. Our tool is implemented in around 9,500 lines of Python code.
Some interesting parts of the source codes are as follows:

- stlmc/src/stlmcPy/encoding/
    This directory contains the implementation of direct (i.e., 1-step) and 2-step solving algorithms, 
    explained in Sec. 4.2 and 4.3 of the paper, respectively. The 1-step solving algorithm is implemented
    in 'monolithc.py' and 2-step solving algorithm is implemented in 'enumerate.py', where each file contains 
    the implementation of the epsilon strengthening and encoding of Boolean STL model checking.

- stlmc/src/stlmcPy/objects/algorithm.py:
    This directory contains the implementation of SMT parallelization algorithm. The STLmc tool uses the 
    implementation of the solving algorithms in 'src/stlmcPy/encoding' and the implementation of the 
    parallelization of this directory together to perform the 2-step parallel algorithm, explained in Sec. 4.3.

- stlmc/src/stlmcPy/solver:
    This directory contains the implementation of the STLmc SMT solving interface, described as 
    'SMT solving interface' in Fig. 4 of our paper. We connect three SMT solvers (i.e., Z3, Yices2, 
    and dReal) using the interface. Each connection is implemented in a file <SOLVER_NAME>.py under 
    this directory, where <SOLVER_NAME> is one of {'z3', 'yices', 'dreal'}.




======================================================
8. The Structure of the Benchmark Model Directories 
======================================================


In this section, we explain the structure of the benchmarks model directories 
of our artifact. We provide benchmark models and their configurations in the 
subdirectory 'benchmarks/', placed at the top directory 'CAV2022-AeC'. 
There are two subdirectories in the 'benchmarks': one for the benchmarks 
of the paper (i.e., 'benchmarks/paper') and the other for the additional 
benchmarks (i.e., 'benchmarks/additional).

Each model is placed in the directory of the same name, with four configuration 
files. For the benchmarks of our paper, the benchmark models and corresponding 
configuration files are placed in the directory, named '<MODEL>-<DYNAMICS>' 
where it is one of {bat-linear, wat-linear, car-poly, rail-poly, thm-ode, oscil-ode} 
and <LABEL> is one of {f1,f2,f3}:

- benchmarks/paper/<MODEL>-<DYNAMICS>/
  * <MODEL>.model: the STLmc model <MODEL>
  * <MODEL>.cfg: basic model configuration
  * <MODEL>-<LABEL>.cfg: configuration considering the goal '<LABEL>'

For example, the autonomous car model with polynomial dynamics of our paper 
is placed in the directory 'benchmarks/paper/car-poly' as follows:

- benchmarks/paper/car-poly
  * car.model: a model of an autonomous driving of two cars
  * car.cfg: basic model configuration
  * car-f1.cfg: configuration considering the goal 'f1'
  * car-f2.cfg: configuration considering the goal 'f2'
  * car-f3.cfg: configuration considering the goal 'f3'


Additional models and configuration files are placed in the directory 
'benchmarks/additional/', following the same structure (i.e., the benchmark models 
and configuration files are included in the <MODEL>-<DYNAMICS> directory which is one of 
{bat-poly, bat-ode, wat-poly, wat-ode, car-linear, car-ode, rail-linear, rail-ode, 
thm-linear, the-poly, nav-ode, space-ode} and <LABEL> is one of {f1,f2,f3}).




======================================================
9. More usage of the STLmc Tool 
======================================================


There are several analysis parameters for the STLmc tool, such as a discrete bound, 
a robustness threshold, and an underlying SMT solver, etc. These parameters can be 
set using: (1) a command-line interface and (2) configuration files. The STLmc tool 
also provides the script 'stlmc-vis' to draw counterexample signals and robustness degrees. 

In this section, we demonstrate an example of changing analysis parameters using the
command-line interface and an example of changing analysis parameters using 
configuration files. Finally, we explain more details of the script 'stlmc-vis' 
and the visualization configuration file using an example.

(1) Using a command-line interface

We demonstrate how to analyze all STL formulas for the two networked thermostat controller 
model in the subdirectory 'benchmarks/paper/thm-ode'. 

The STLmc tool can limit duration in one mode using the 'time-horizon' option.
For example, if the 'time-horizon' is 5, a discrete jump should occur within 5.

We can use the script 'stlmc' in the 'stlmc/src' directory to start the STLmc tool. The 
following command finds a counterexample of the formula 'f3' of the thermostat model 
at bound 4 with respect to robustness threshold 2 using parallelized 2-step algorithm and dReal:

user@VB:~/CAV2022-AeC/stlmc/src$./stlmc ../../benchmarks/paper/thm-ode/therm.model -bound 5 -time-bound 30 -threshold 2 -goal f3 -two-step -parallel -visualize -time-horizon 7 -solver dreal

In VM, it will take about 90 seconds on AMD Ryzen 9 3.3GHz with quad-core and 4GB of memory.

(2) Using configuration files

We demonstrate how to analyze a specific STL formula for the thermostat controller
 model in the subdirectory 'benchmarks/paper/thm-ode' and using the configuration files.

We can instantiate analysis parameters such as a discrete bound, a time bound, and other 
parameters by modifying a model configuration file and a model-specific configuration file. 
The model configuration file specifies some analysis parameters related to a model and
the model-specific configuration file is used to specify different analysis parameters
for each STL formula of the model.

We can run the same case in Section 9.(1) using configuration files.
The model configuration file for the thermostat controller is in 
'benchmarks/paper/thm-ode/therm.cfg'. The contents of the file are as follows:

common {
    time-bound = 30
    bound = 5
    solver = "dreal"
    verbose = "true"   # print verbose messages
    two-step = "true"
    parallel = "true"
}

Make a new model specific configuration file, named 'new-therm-f3.cfg', for the thermostat 
controller as follows:

common {
    threshold = 2.0
    time-horizon = 7
    goal = "f3"
    visualize = "true"
}

The following command verifies the formula 'f3' with the same options in Section 9.(1)

user@VB:~/CAV2022-AeC/stlmc/src$./stlmc ../../benchmarks/paper/thm-ode/therm.model -model-cfg ../../benchmarks/paper/thm-ode/therm.cfg -model-specific-cfg new-therm-f3.cfg

(3) More details on the script 'stlmc-vis'

The script 'stlmc-vis' provides several options to generate counterexample witnesses. 
The command './stlmc-vis -h' shows more details about arguments.
There are three command line arguments as follows: 

user@VB:~/CAV2022-AeC/stlmc/src$ ./stlmc-vis [-output <FORMAT>] \
                                       [-cfg <CONF_FILE>] \
                                       <FILE>

The script supports two output formats: 'html' and 'pdf'. The default value of the '-output' 
is 'html'. The default value of the '-cfg' option is a configuration file with the same name 
as the input counterexample file.

The configuration file contains information about labeling variables, that start with '#', groups  
for drawing counterexample witness graphs, and an output format of the graphs.
For example, consider 'therm_b5_f3_dreal.cfg' that is generated by running the command in 
Section 9.(1). The contents of the file are as follows: 
{
# state variables: x0 , x1
# f3_0 ---> ([][0.0,10.0] ((x0 > 23) R[0.0,inf) ((x0 - x1) >= 4)))
# f3_1 ---> ((x0 > 23) R[0.0,inf) ((x0 - x1) >= 4))
# f3_2 ---> (x0 > 23)
# f3_3 ---> ((x0 - x1) >= 4)
output = html # pdf
group { 
}
}     

The robustness degrees graphs for 'f3_0' and 'f3_1' can be drawn separately by modifying 
'therm_b5_f3_dreal.cfg' as follows:

{
# state variables: x0 , x1
# f3_0 ---> ([][0.0,10.0] ((x0 > 23) R[0.0,inf) ((x0 - x1) >= 4)))
# f3_1 ---> ((x0 > 23) R[0.0,inf) ((x0 - x1) >= 4))
# f3_2 ---> (x0 > 23)
# f3_3 ---> ((x0 - x1) >= 4)
output = html # pdf
group { (f3_0), (f3_1)
}
}

The following command creates an html file named 'therm_b5_f3_dreal.counterexample.html',

user@VB:~/CAV2022-AeC/stlmc/src$./stlmc-vis therm_b5_f3_dreal.counterexample
  
Note that continuous state variables and STL subformulas cannot be grouped together. 
For example, 'x0' and 'f3_1' cannot be in the same group. 

See our tool manual for more details. 




======================================================
10. Running the Additional Experiments 
======================================================


In this section, we explain how to run additional experiments of our technical report. We consider 
the following additional benchmark models: bat-poly, bat-ode, wat-poly, wat-ode, car-linear, car-ode, 
rail-linear, rail-ode, thm-linear, thm-poly, nav-ode, space-ode. See the STLmc technical report 
(https://stlmc.github.io/documents) for more details. 

We can reproduce experiments for the additional benchmark models, using the script 'run-exp'
in the 'scripts' directory. The script 'run-exp' provides options to run the experiments. 
The command './run-exp -h' shows more details about arguments. There are three (two optional) 
command line arguments as follows: 

user@VB:~/CAV2022-AeC/scripts$ ./run-exp <PATH TO MODELS> 
                                            [-t <TIMEOUT>] 
                                            [-o <OUT_DIR>]

The script takes paths that include STLmc model files (or STLmc model files) to be analyzed.
The '-t' and '-o' are optional parameters. The '-t' sets a timeout in seconds and '-o' sets a name 
of a log directory (i.e., the directory where the result logs are saved).
 
By default, the script generates log files in the 'log' subdirectory, placed in the current directory. 
When '-o' is set, the name of the directory is changed, following the parameter.

Additional benchmark models are located in 'benchmarks/additional' directory.
Thus, the following command runs all additional benchmark models with a timeout of 1 hour:

user@VB:~/CAV2022-AeC/scripts$ ./run-exp ../benchmarks/additional/ -t 3600

In VM, it will take about 3 hours on AMD Ryzen 9 3.3GHz with VM quad-core and 4GB memory. 

Following the Unix standard, the <PATH TO MODELS> may contain paths, including the star (*) wildcard.
For example, we can run the 'thm-linear' model and the 'thm-poly' model using 
the following command:

user@VB:~/CAV2022-AeC/scripts$ ./run-exp ../benchmarks/additional/thm-* -t 3600 

To generate a table from the log files, we provide the script 'gen-table'. There is one (optional) 
command-line arguments as follows: 

user@VB:~/CAV2022-AeC/scripts$ ./gen-table [<PATH TO LOG DIRECTORY>]

The default value of the '<PATH TO LOG DIRECTORY>' is the 'log' subdirectory 
in the current directory. For example, the following command generates the
'log-table.html' file using the log files in the 'log' directory: 

user@VB:~/CAV2022-AeC/scripts$ ./gen-table

Note that the script 'gen-table' generates CSV files from the log files and then uses the CSV to generate 
the table (e.g., the above command generates 'log-report.csv' as well).

The generated table contains the following columns for each case of the experiment 
described in Sec.5  of our paper:

- dynamics: the continuous dynamics of the model
- model: the name of the benchmark model
- label: the labels of the STL formulas for the model (f1, f2, or f3)
- STL formula: the STL formula corresponding to the label
- time bound: the time bound for the model
- threshold: the robustness threshold
- size: the size of generated SMT encoding
- time: the execution time of the selected algorithm
- result: the result of the STL model checking
- bound: the bound at which the selected algorithm is terminated
- scenarios: the number of minimal scenarios
- algorithm:	the model checking algorithm, either 1-step or 2-step

Each row of the table corresponds to an item in Table 2 of the paper. 
For example, the following table row corresponds to the case of (Linear, Wat, f2)
in Table 2 of the paper:

linear, wat, f2, ((<>[1.0,10.0) (x2 < 5.5)) U[2.0,5.0] (x1 >= 5)), 20, 0.1, 1878, 4.22, FALSE, 4, -, 1-step.

We also provide the script 'gen-report' to generate CSV report. This report contains the same columns as above
and each row of the CSV corresponds to an item in Table 2 of the paper. 

The script 'gen-report' has one (optional) command line argument as follows:

user@VB:~/CAV2022-AeC/scripts$ ./gen-report [<PATH TO LOG DIRECTORY>]

The default value of the '<PATH TO LOG DIRECTORY>' is 'log'. The script reads log files in the 
'<PATH TO LOG DIRECTORY>' and generates CSV file with the name '<PATH TO LOG DIRECTORY>-report.csv'. 
For example, the following command generates the 'log-report.csv' file from the log files in the 
'log' directory: 

user@VB:~/CAV2022-AeC/scripts$ ./gen-report




======================================================
11. Supplemental Materials
======================================================


We provide a user manual that explains the modeling language of the STLmc tool 
and how to use the tool. We also provide a technical report with additional experiments.

The user manual and the technical report can be downloaded from
https://stlmc.github.io/documents.




======================================================
12. Running the Artifact without VM
======================================================


To run the STLmc tool in other than provided virtual machine, 
the followings are required:

- Python version 3.8.6 or newer: https://www.python.org/downloads/

- JAVA 8 or newer: https://openjdk.java.net/install/

- Python3-pip: https://pypi.org/
    Please make sure that pip is up-to-date. Otherwise some Python libraries STLmc used, such as numpy, 
    may fail to be installed.

- Yices2: https://github.com/SRI-CSL/yices2/

    Our artifact needs MCSAT-enabled version of Yices2. Please follow the below installation steps to get 
    this specific version of Yices2:

    * Ubuntu

      To install Yices on Ubuntu, do the following:
    
      $sudo apt install software-properties-common
      $sudo add-apt-repository ppa:sri-csl/formal-methods
      $sudo apt-get update
      $sudo apt-get install yices2-dev


    * MacOS

      To install on macOS, use homebrew:

      $brew install SRI-CSL/sri-csl/yices2


    Remark: Some experiments may not run properly on the following architectures: Apple MacBook Pro 2015 
    or earlier (Yices 2.6 with QF-NRA is not working).


- Z3: https://github.com/Z3Prover/z3/

    * Ubuntu

      Normally, Z3 solver is automatically installed when downloading its Python3 package (i.e., using pip3 install z3-solver).

    * MacOS 

      Normally, Z3 solver is automatically installed as in Linux environment. But for some cases, we found that one may need 
      to install Z3 binaries manually. This can be done using the following command:

      $brew install z3


- Gnuplot: http://www.gnuplot.info/

    STLmc uses Gnuplot for counterexample generation.
    
    * Ubuntu
    
      $sudo apt install gnuplot
    
    * MacOS
   
      $brew install gnuplot



To install our artifact, follow the below instruction steps:

1. Download and unzip the archive file (CAV2022-AeC-NoN-VM.zip).
2. Install the following python packages:
    
  - pip3 install termcolor yices z3-solver antlr4-python3-runtime==4.9.1 sympy numpy bokeh scipy
    
3. Run the following command:

  - cd CAV2022-AeC-NoN-VM && make
  
4. Use the following command to run smoke tests for our installation:
  
  - make test

  This command requires sudo permission.

5. If the tests succeed, you will see the following messages:

  start smoke test ...
  [exec] Python: pass
  [exec] Yices: pass
  [exec] dReal: pass
  [exec] Z3: pass
  [exec] Java: pass
  [exec] Gnuplot: pass
  [file] Config: pass
  [smt] dReal
    ./tests/smt2/dreal/01.smt2: pass
    ./tests/smt2/dreal/02.smt2: pass
  [smt] Z3
    ./tests/smt2/z3/01.smt2: pass
    ./tests/smt2/z3/02.smt2: pass
  [smt] Yices
    ./tests/smt2/yices2/01.smt2: pass
    ./tests/smt2/yices2/02.smt2: pass
  [tool] STLmc
    ./tests/stlmc/01.model: pass
    ./tests/stlmc/02.model: pass

STLmc uses the following SMT solvers as its underlying SMT solvers:

* Z3: https://github.com/Z3Prover/z3/
* Yices2: https://github.com/SRI-CSL/yices2/
* dReal: https://github.com/dreal/dreal3/

The archive file already contains dReal in the directory 'CAV2022-AeC-NoN-VM/stlmc/3rd_party'.

See our webpage https://stlmc.github.io/cav2022-artifact/ for more details.
