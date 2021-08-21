## Overview

There are three ways to run our artifact.

      (1) Using the VirtualBox Image 

      (2) Installation from Source Code

      (3) Installation from Docker 
      
## Using the VirtualBox Image

You can run the experiments using VirtualBox (www.virtualbox.org). 

A Vritualbox image 'ase2021.ova' contains the benchmark models and scripts for the experiments. 
You can download the image from https://doi.org/10.5281/zenodo.5106005.

A minimum system requirement is as follows:

  - Cores: 4

  - RAM: 12288 MB (12 GB)

In the virtual machine, our artifact is located in the directory 
'home/ase2021/stlmc-ase2021'. The password of the image is "ase2021".

   Please see [README.md](README.md#running-the-experiments) for instructions to run the experiments.

---

## Installation from Source Code

### Prerequisites

To build the artifact from the source, you need:

- Ubuntu 18.04
- Python version 3.8.x or newer
- JAVA 8: https://openjdk.java.net/install/
- Python3-pip: https://pypi.org
- GNUPLOT: http://www.gnuplot.info

### Installation

1. Download Yices2 (https://github.com/SRI-CSL/yices2):

   ~~~
   sudo apt install software-properties-common
   sudo add-apt-repository ppa:sri-csl/formal-methods
   sudo apt-get update
   sudo apt-get install yices2-dev
   ~~~

2. Install the following python packages:

   ~~~
   pip3 install termcolor yices antlr4-python3-runtime
   ~~~

3. Download the source code and unzip it (https://github.com/stlmc/stlmc/releases/tag/ase2021).
4. Run the following commands:

   ~~~
   cd stlmc-ase2021
   make
   ~~~

5. Restart the terminal.

6. Finish!!

   Please see [README.md](README.md#running-the-experiments) for instructions to run the experiments.

---

## Installation from Docker

You can run the experiments using Docker (https://docs.docker.com).

1. Download docker "ubuntu: 18.04" and execute the docker:

   ~~~
   docker run ubuntu:18.04 
   docker run --restart always --name ubuntu_18.04 -dt ubuntu:18.04 
   docker ps
   docker exec -it ubuntu_18.04 /bin/bash 
   ~~~

2. Download prerequisite packages:

   ~~~
   apt update
   apt install -y python3 python3-pip openjdk-8-jdk software-properties-common wget nano unzip less gnuplot
   ~~~

3. Download Yices2 (https://github.com/SRI-CSL/yices2):

   ~~~
   add-apt-repository ppa:sri-csl/formal-methods
   apt update
   apt install -y yices2-dev
   ~~~

4. Upgrade Python3 version to 3.8:

   ~~~
   add-apt-repository ppa:deadsnakes/ppa
   apt update
   apt install python3.8
   update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.8 11
   update-alternatives --config python3 
   ~~~

5. Do the same STEP "2 ~ 5" of [Installation from Source Code](INSTALL.md#installation) 

6. Finish!!

   Please see [README.md](README.md#running-the-experiments) for instructions to run the experiments. 

