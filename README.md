# InfOCF

Library to perform non-monotonic inference according to p-entailment, system-z, system-w and c-inference.

### Installation

Requirements listed in `requirements.txt` can be installed using pip in venv. We used python 3.11 while building this version of the library.

Optionally the whole environment can be installed using the nix package manager by simply running `nix develop` in the project dir containing the flake.nix file (or by running `nix develop .#withNeovim` if neovim with nodejs support for plugins is desired in environment).


### Usage

In `show.py` we demonstrate the use of the InfOCF library, performing multiple inferences according to all implemented inference systems with differing solvers while setting other optional parameters,
iterating over belief base and query files and concatenating the results.

Please refer to `show_minimal.py` for a more minimalistic demonstration.
