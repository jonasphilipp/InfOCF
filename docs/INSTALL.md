# Installation

### This guide is meant for Linux users. For other operating systems check the resources below.

Download the repository by cloning it or downloading the archive.

## Method 1: Installing packages using pip

### Set up venv
You can create a virtual environment using venv:
```
python -m venv /path/to/new/virtual/environment
```
Start your virtual environment using
```
source /path/to/new/virtual/environment/bin/activate
```
or connect it to your IDE. Some IDEs can set up venv for you.

### Install required packages

The requirements listed in `requirements.txt` can be installed using pip in venv using the command

```
pip install -r /path/to/requirements.txt
```

The `requirements.txt` can be found at `/InfOCF-main`.

We used python 3.11 while building this version of the library.

Note: On some operating systems Yices2 needs to be installed separately. If issues persist after installing, try removing the yices python package.

## Method 2: Using nix
Optionally the whole environment can be installed using the nix package manager by simply running `nix develop` in the project dir containing the flake.nix file (or by running `nix develop .#withNeovim` if neovim with nodejs support for plugins is desired in environment).

## Resources
pip: https://pypi.org/project/pip/

venv: https://docs.python.org/3/library/venv.html

Yices2: https://yices.csl.sri.com/
