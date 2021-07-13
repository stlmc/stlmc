## Overview

We support two ways to run our artifact:

   ​	(1) Using the VirtualBox Image

   ​	(2) Installing from Source Code

## Using the VirtualBox Image

You can run the experiments using VirtualBox (www.virtualbox.org). 

A Vritualbox image 'ase2021.ova' contains the benchmark models and scripts for the experiments. 
You can download the image from https://www.dropbox.com/home/ase2021.

A minimum system requirement is a dual-core machine with 2048 MB memory. In the virtual machine, 
our artifact is located in the directory 'home/ase2021/stlmc'. The password of the image is "ase2021".

---

## Installing from Source Code

### Prerequisites

To build the artifact from the source, you need:

- Ubuntu 18.04
- Python version 3.8.* or newer
- JAVA 8: https://openjdk.java.net/install/
- Python3-pip: https://pypi.org

### Installation

1. Download Yices2 (https://github.com/SRI-CSL/yices2):

   ~~~
   sudo add-apt-repository ppa:sri-csl/formal-methods
   sudo apt-get update
   sudo apt-get install yices2-dev
   ~~~

2. Install following python packages:

   ~~~
   pip3 install termcolor yices antlr4-python3-runtime
   ~~~

3. Download the source code (https://github.com/stlmc/stlmc/releases/tag/ase2021).
4. Unzip the downloaded file.
5. Run the following commands:

   ~~~
   cd stlmc-ase2021
   make antlr
   ~~~

6. Finish!!

   Please see [README.md](README.md#running-the-experiments) to run the experiments. 

