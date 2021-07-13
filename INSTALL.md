
## Using the VirtualBox Image

You can run the experiments using VirtualBox (www.virtualbox.org). 

A Vritualbox image 'stlmc-artifact.ova' contains the benchmark models and scripts for the experiments. 
You can download the image from https://www.dropbox.com/home/ase2021.

A minimum system requirement is a dual-core machine with 2048 MB memory. In the virtual machine, 
our artifact is located in the directory 'home/ase2021/stlmc'. The password of the image is "ase2021".

---

## Running the Experiment without VM

We support scripts to install our artifact on Ubuntu 18.04.

1. Download the source code (https://github.com/stlmc/stlmc/releases/tag/ase2021).

2. Unzip the downloaded file.

3. Run the following commands:

~~~
cd stlmc-ase2021
sudo apt install make
sh permission.sh
sudo make python
~~~

4. Restarting the terminal window.
5. Run the following commands:

~~~
cd stlmc-ase2021
sudo make
make setpython
~~~
5. Finish!!

   Please see [README.md](README.md#running-the-experiments) to run the experiments. 


