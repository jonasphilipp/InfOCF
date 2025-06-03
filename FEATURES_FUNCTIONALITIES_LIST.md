# FEATURES

### Modularity

    - Clear separation between parser, inference algorithms, optimizers, and user-facing helpers.
    - Each inference system implemented as its own subclass -> easy to plug in new ones.

### Performance
    - Order-of-magnitude speed-ups vs. legacy code (algorithmic & MaxSAT improvements).
    - Multiprocessing option for parallel query computation across CPU cores.

### Reuse of Intermediate States & Caching
    - keeps partitions, CNF encodings, optimized CSPs, ID pools to avoid recomputation.

### Detailed Timing & Timeout Control
    - Separate timeouts for preprocessing, per-query inference, and total budget.
    - Millisecond-precision measurements stored alongside each result.

### Pandas DataFrame Output
    - Unified results table incl. meta-data (signature size, solver, timings, etc.).
    - Facilitates downstream analysis, plotting, or CSV/Excel export.

### SMT-Solver Independence (PySMT abstraction)
    - PySMT layer lets users switch among Z3, CVC5, MathSAT … via a single flag.
    - No smt-solver-specific code scattered throughout the library.

### Extensibility (plug-in solvers & inference systems)
    - Factory helpers (`create_optimizer`, `create_inference_instance`) auto-instantiate classes.
    - New Partial-MaxSAT optimizers can register through the `Optimizer` interface.

### Nix Environment
    - `flake.nix` provides fully reproducible dev & CI environment with pinned toolchain.

# FUNCTIONALITIES

-Parsing of a BB, translation into internal format

-checking strong and weak consistency of a BB

-computing the (system Z) tolerance partition of a BB

-inference with p-entailment

-inference with system Z

-inference with system W (RC2 & Z3 implementations for PMAXSAT Problems)

-inference with lexicographic inference

-inference with c-inference 

-Tseitin CNF transformation of belief bases & queries

-calculation of minimal correction subsets via Partial MaxSAT


# New WP8 Features and Functionalities (PreOCF Module)

### Creation of Pre-Ordinal Conditional Function (PreOCF) objects
    - `init_system_z`: derive a world-ranking from a belief base via System Z.
    - `init_random_min_c_rep`: initialise with a random minimal-correction representation. (not complete yet)
    - `init_custom`: supply arbitrary user-defined ranks.

### Rich ranking operations
    - `rank_world`, `compute_all_ranks`: compute/complete world ranks on demand.
    - `formula_rank`: minimal rank of worlds satisfying a formula.
    - `is_ocf`: validity check that every world has a non-negative rank.

### Conditional reasoning helpers
    - `conditional_acceptance`: test acceptance of a conditional (B|A).

### Signature manipulations
    - `marginalize`: project the PreOCF onto a smaller variable set.
    - Conditionalization utilities (`filter_worlds_by_conditionalization`, etc.).

### Conversions between representations
    - `ranks2tpo`, `tpo2ranks`: translate between rank dictionaries and total preorders.
    - `ranks_verbose` property for human-readable world names.

### Persistence & reproducibility
    - In-memory key-value store (`save`/`load`).
    - Disk serialisation to JSON / pickle (`save_persistence`, `load_persistence`).
    - JSON OS-agnostic

### Utility helpers
    - `create_bitvec_world_dict` for generating complete world dictionaries.
    - Helpers to convert bit-vectors <-> SMT variables (`symbolize_bitvec`).