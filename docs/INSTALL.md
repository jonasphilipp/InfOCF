# Installation

TODO: Update these descriptions. Give a step by step guide.

## Method 1: Installing packages manually
Requirements listed in `requirements.txt` can be installed using pip in venv. We used python 3.11 while building this version of the library.

## Method 2: Using nix
Optionally the whole environment can be installed using the nix package manager by simply running `nix develop` in the project dir containing the flake.nix file (or by running `nix develop .#withNeovim` if neovim with nodejs support for plugins is desired in environment).
