
Creates somewhat random, large CKB's, which are used to benchmark how fast the compillation algorithm is.
No interface implemented at the moment, change the parameters in `sampling.py`, then run `python sampling.py`



### upperBound.py
the method 'sampling' takes as input a list of variables (represented as strings), and a filename.
If the amount of variables is n, it prints into the file with the filename a CKB, such that 2^(n-1)
is the smallest possible solution for at least one eta.
See `Nonmonotonic reasoning from conditional knowledge bases with system W` from Komo and Beierle for
the theoretical details


### sampling.py
Attempts to model CKB's with a lot of 'exceptions within exceptions within exceptions' behavior.

### trueRandomSampling.py
Creates random CKB benchmark datasets.

The default mode is now `natural-repeated-vars`, which samples conditionals from a
neutral formula distribution that allows variables to occur repeatedly in one
formula, classifies each generated belief base as strongly or weakly consistent,
and writes it below `natural-repeated-vars/{strong,weak}`. This is the preferred
mode for weak/strong benchmark comparisons because no conditional is artificially
injected to force weak consistency.

The older read-once formula generator is still available as `natural-read-once`
for continuity with ECSQARU-style random generation. The older explicit
`(Bottom | p)` weak stress-test generator is still available as
`targeted-literal-bottom`; it should not be treated as the canonical weak
generator.

Examples:

```bash
uv run python benchmarks/trueRandomSampling.py \
  --mode natural-repeated-vars \
  --combination 60/60 \
  --samples-per-combination 25

uv run python benchmarks/trueRandomSampling.py \
  --mode natural-read-once

uv run python benchmarks/trueRandomSampling.py \
  --mode targeted-literal-bottom
```
