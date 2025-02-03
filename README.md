# InfOCF - Reasoning With Conditional Belief Bases

InfOCF is part of a project for realizing nonmonotonic reasoning from conditional belief bases and making these tools easily available.

InfOCF is a library providing implementations for non-monotonic inference operators including p-entailment[^1], system Z[^2], system W[^3], and c-inference[^4].
The implementations use current SAT and MaxSAT solvers such as Z3.
p-Entailment is implemented based on SAT checks.
System Z and system W are implemented using the algorithms SZinf and SWinf[^6] using MaxSAT solvers.
c-Inference is implemented by using its characterization by a system of inequations[^4], which are minimized using MaxSAT solving and then encoded into an SMT problem[^7].

InfOCF supports parsing conditional belief bases from files in the `.cl`-format (see [cl syntax description](docs/CL_SYNTAX.md)).

The main functions of InfOCF are available in the easy-to-use online reasoning plattform [InfOCF-Web 2.0](https://www.fernuni-hagen.de/wbs/research/infocf-web/).
InfOCF-Web 2.0 is build on top of InfOCF and supports nonmonotonic reasoning from conditional belief bases with various inductive inference operators[^5].

[^1]: Kraus, Lehmann, Magidor: *Nonmonotonic Reasoning, Preferential Models and Cumulative Logics*. Artificial Intelligence 44(1-2), 167–207 (1990)
[^2]: Pearl: *System Z: A natural ordering of defaults with tractable applications to nonmonotonic reasoning*. Proceedings of TARK’1990, pp. 121–135. Morgan Kaufmann (1990)
[^3]: Komo, Beierle: *Nonmonotonic reasoning from conditional knowledge bases with system W*. Annals of Mathematics and Artificial Intelligence 90(1), 107–144 (2022).
[^4]: Beierle, Eichhorn, Kern-Isberner, Kutsch: *Properties and interrelationships of skeptical, weakly skeptical, and credulous inference induced by classes of minimal models*. Artificial Intelligence 297, 103489 (2021).
[^5]: Beierle, Haldimann, Sanin, Schwarzer, Spang, Spiegel, von Berg: *Scaling up reasoning from conditional belief bases*. SUM 2024, LNCS Vol. 15350, pages 29–44. Springer (2024).
[^6]: Beierle, Spang, Haldimann: *A partial maxsat approach to nonmonotonic reasoning with system W*. The International FLAIRS Conference Proceedings 37(1) (2024).
[^7]: von Berg, Sanin, Beierle: *Scaling up nonmonotonic c-inference via partial MaxSAT problems*. FoIKS-2024, LNCS Vol. 14589, pp. 182–200. Springer (2024).

### Installation

To install InfOCF follow the steps in the [installation guide](docs/INSTALL.md).

### Usage

The usage of InfOCF is demonstrated in [show.py](docs/show.py).

A small example showing how to get started can be found in [show_minimal.py](docs/show_minimal.py).
