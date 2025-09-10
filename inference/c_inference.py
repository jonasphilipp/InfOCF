"""
C-Inference Operator for Conditional Belief Bases

This module implements the c-inference operator for conditional belief bases.
"""

import logging
from time import perf_counter_ns

from pysat.formula import WCNF
from pysmt.shortcuts import (
    GE,
    GT,
    INT,
    LE,
    LT,
    And,
    Int,
    Not,
    Plus,
    Solver,
    Symbol,
    is_sat,
)

from inference.conditional import Conditional
from inference.deadline import Deadline
from inference.inference import Inference
from inference.optimizer import create_optimizer
from inference.tseitin_transformation import TseitinTransformation
from infocf.log_setup import get_logger

# Configure module logger
logger = get_logger(__name__)


def makeSummation(minima: dict) -> dict[int, list]:
    """
    Convert minimal correction subsets to PySMT sum expressions.

    This function transforms dictionaries of minimal correction subsets into
    PySMT Plus expressions representing the sum of eta variables for each subset.
    Used in the constraint encoding process for c-inference.

    Parameters
    ----------
    minima : dict
        Dictionary where keys are indices and values are lists of minimal
        correction subsets (each subset is a list of integers)

    Returns
    -------
    dict[int, list]
        Dictionary mapping indices to lists of PySMT Plus expressions

    Notes
    -----
    Each minimal correction subset is converted to a sum of eta variables.
    Empty subsets are represented as Int(0).

    Examples
    --------
    >>> minima = {0: [[1, 2], [3]]}
    >>> result = makeSummation(minima)
    >>> # result[0] contains [Plus([eta_1, eta_2]), Plus([eta_3])]
    """
    results = dict()
    for index, summ in minima.items():
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug("summ %s", summ)
        interim = []
        for subsum in summ:
            if logger.isEnabledFor(logging.DEBUG):
                logger.debug("subsum %s", subsum)
            if subsum:
                interim.append(Plus([Symbol(f"eta_{i}", INT) for i in subsum]))
            else:
                interim.append(Int(0))  # Or use 0 directly
        results[index] = interim
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug("results %s", results)
    return results


def freshVars(i: int) -> tuple:
    """
    Generate fresh PySMT variables for minimal value encoding.

    Creates a pair of fresh integer variables used in the minima encoding
    process of c-inference. These variables represent the minimum values
    for verification and falsification constraints.

    Parameters
    ----------
    i : int
        Index used to create unique variable names

    Returns
    -------
    tuple of pysmt.FNode
        A tuple (mv_i, mf_i) where mv_i is the verification minimum variable
        and mf_i is the falsification minimum variable

    Examples
    --------
    >>> mv, mf = freshVars(0)
    >>> # Creates variables 'mv_0' and 'mf_0'
    """
    if logger.isEnabledFor(logging.DEBUG):
        logger.debug("freshVars %s", i)
    return Symbol(f"mv_{i}", INT), Symbol(f"mf_{i}", INT)


def minima_encoding(mv: int, ssums: list) -> list:
    """
    Encode minimum value constraints for a set of sums.

    Creates PySMT constraints that ensure a variable mv is less than or equal
    to all values in ssums, and that mv is greater than or equal to at least
    one value in ssums. This implements the "minimum of sums" encoding.

    Parameters
    ----------
    mv : pysmt.FNode
        The variable to constrain (minimum value variable)
    ssums : list
        List of PySMT expressions representing sums

    Returns
    -------
    list of pysmt.FNode
        List of PySMT constraints implementing the minima encoding

    Notes
    -----
    The encoding ensures: mv ≤ min(ssums) ∧ mv ≥ min(ssums)
    This is implemented as: ∀s∈ssums: mv ≤ s ∧ ∃s∈ssums: mv ≥ s

    Examples
    --------
    >>> mv, _ = freshVars(0)
    >>> sums = [Symbol('eta_1', INT), Plus([Symbol('eta_2', INT), Symbol('eta_3', INT)])]
    >>> constraints = minima_encoding(mv, sums)
    """
    ands = [LE(mv, i) for i in ssums]
    ors = Not(And([LT(mv, i) for i in ssums]))
    ands.append(ors)
    if logger.isEnabledFor(logging.DEBUG):
        logger.debug("minima_encoding %s", ands)
    return ands


class CInference(Inference):
    """
    C-Inference operator implementation using constraint satisfaction problems.

    C-inference is a sophisticated inference operator for conditional belief bases
    that uses minimal correction subsets and constraint satisfaction problems (CSPs)
    to determine whether a conditional is entailed by a belief base.

    The algorithm works by:
    1. Preprocessing the belief base into CNF form
    2. Computing minimal correction subsets for verification and falsification
    3. Encoding the inference problem as a CSP
    4. Using SMT solving to determine entailment

    This operator is particularly powerful for handling complex inference scenarios
    where other operators may be too weak or too strong.

    Parameters
    ----------
    *args
        Variable positional arguments passed to parent Inference class
    **kwargs
        Variable keyword arguments passed to parent Inference class.
        The parent class expects an 'epistemic_state' dictionary containing:
        - 'belief_base': BeliefBase instance
        - 'smt_solver': str, name of SMT solver to use
        - Additional keys will be initialized automatically

    Attributes
    ----------
    epistemic_state : dict
        Internal state containing belief base, CSP constraints, and computed minima
    base_csp : list
        Base constraint satisfaction problem encoding the belief base

    Examples
    --------
    >>> from infocf import BeliefBase, CInference
    >>> from inference.conditional import Conditional
    >>> from pysmt.shortcuts import Symbol
    >>>
    >>> # Create belief base
    >>> p, q, r = Symbol('p'), Symbol('q'), Symbol('r')
    >>> conditionals = {
    ...     0: Conditional(q, p, '(q|p)'),
    ...     1: Conditional(r, q, '(r|q)')
    ... }
    >>> bb = BeliefBase(['p', 'q', 'r'], conditionals, 'example')
    >>>
    >>> # Create c-inference instance
    >>> epistemic_state = {'belief_base': bb, 'smt_solver': 'z3'}
    >>> inference = CInference(epistemic_state)
    >>>
    >>> # Query entailment
    >>> result = inference.query('(r|p)')  # Is (r|p) entailed?

    Notes
    -----
    C-inference uses a two-phase approach:
    - **Verification phase**: Computes minimal correction subsets when the query
      is added to the belief base
    - **Falsification phase**: Computes minimal correction subsets when the
      negated query is added to the belief base
    - **Entailment decision**: Query is entailed if verification minima are
      smaller than falsification minima

    The operator is computationally expensive but provides precise inference
    results for complex scenarios.

    References
    ----------
    .. [1] Beierle, Eichhorn, Kern-Isberner, Kutsch: "Properties and interrelationships
           of skeptical, weakly skeptical, and credulous inference induced by classes
           of minimal models". Artificial Intelligence 297, 103489 (2021)

    .. [2] von Berg, Sanin, Beierle: "Scaling up nonmonotonic c-inference via partial
           MaxSAT problems". FoIKS-2024, LNCS Vol. 14589, pp. 182–200. Springer (2024)
    """

    def __init__(self, *args, **kwargs):
        """
        Initialize the C-Inference operator.

        Sets up the epistemic state and initializes data structures for
        storing minimal correction subsets used in the inference process.

        Parameters
        ----------
        *args
            Positional arguments passed to parent Inference class
        **kwargs
            Keyword arguments passed to parent Inference class
        """
        super().__init__(*args, **kwargs)
        if "vMin" not in self.epistemic_state:
            self.epistemic_state["vMin"] = dict()
        if "fMin" not in self.epistemic_state:
            self.epistemic_state["fMin"] = dict()

    def encoding(self, etas: dict, vSums: dict, fSums: dict) -> list:
        """
        Encode minimal correction subset constraints into PySMT constraints.

        Creates a constraint satisfaction problem (CSP) that encodes the
        relationship between eta variables and their minimal correction subsets.
        Each eta variable represents the "rank" or "cost" of a conditional,
        and the constraints ensure that verification minima are less than
        falsification minima for entailed queries.

        Parameters
        ----------
        etas : dict[int, pysmt.FNode]
            Dictionary mapping conditional indices to eta variables
        vSums : dict[int, list]
            Dictionary of verification sum expressions for each conditional
        fSums : dict[int, list]
            Dictionary of falsification sum expressions for each conditional

        Returns
        -------
        list of pysmt.FNode
            List of PySMT constraints encoding the CSP

        Notes
        -----
        For each conditional i, the encoding ensures:
        eta_i > mv_i - mf_i

        where mv_i is the minimum of verification sums and mf_i is the minimum
        of falsification sums. This constraint drives the inference decision.
        """
        csp = []
        for index, eta in etas.items():
            if logger.isEnabledFor(logging.DEBUG):
                logger.debug("eta %s", eta)
                logger.debug("vSums %s", vSums[index])
                logger.debug("fSums %s", fSums[index])
            mv, mf = freshVars(index)
            vMin = minima_encoding(mv, vSums[index])
            fMin = minima_encoding(mf, fSums[index])
            csp.extend(vMin)
            csp.extend(fMin)
            csp.append(GT(eta, mv - mf))
        return csp

    def translate(self) -> list:
        """
        Translate the belief base into a constraint satisfaction problem.

        Creates the base CSP encoding for the entire belief base by:
        1. Creating eta variables for each conditional (representing their "rank")
        2. Converting minimal correction subsets to sum expressions
        3. Encoding the relationships between etas and minima as constraints
        4. Adding non-negativity constraints for eta variables

        Returns
        -------
        list of pysmt.FNode
            Complete CSP encoding of the belief base as PySMT constraints

        Notes
        -----
        The translation creates variables eta_1, eta_2, ..., eta_n for each
        conditional in the belief base. These variables represent the "cost"
        or "rank" of each conditional in the inference process.

        The CSP encodes the relationship between verification and falsification
        minimal correction subsets, which determines entailment decisions.
        """
        logger.debug("translate called")
        eta = {
            i: Symbol(f"eta_{i}", INT)
            for i, _ in enumerate(
                self.epistemic_state["belief_base"].conditionals, start=1
            )
        }
        # defeat= = checkTautologies(self.epistemic_state['belief_base'].conditionals)
        # if not defeat: return False
        gteZeros = [GE(e, Int(0)) for e in eta.values()]
        vSums = makeSummation(self.epistemic_state["vMin"])
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug("vSums %s", vSums)
        fSums = makeSummation(self.epistemic_state["fMin"])
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug("fSums %s", fSums)
        csp = self.encoding(eta, vSums, fSums)
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug("csp %s", csp)
        csp.extend(gteZeros)
        if logger.isEnabledFor(logging.DEBUG):
            logger.debug("csp extended %s", csp)
        return csp

    def _preprocess_belief_base(self, weakly: bool, deadline: Deadline | None) -> None:
        """
        Preprocess the belief base for c-inference.

        Performs the necessary preprocessing steps for c-inference:
        1. Converts the belief base to CNF using Tseitin transformation
        2. Computes minimal correction subsets for all conditionals
        3. Creates the base CSP encoding of the belief base

        Parameters
        ----------
        weakly : bool
            Whether to use weak consistency (passed to Tseitin transformation)
        deadline : Deadline or None
            Timeout deadline for preprocessing operations

        Notes
        -----
        This method is computationally expensive as it needs to compute
        minimal correction subsets for all conditionals in the belief base.
        The results are cached in the epistemic state for use during inference.

        The preprocessing creates:
        - CNF representations of all conditionals
        - Minimal correction subsets for verification (vMin) and falsification (fMin)
        - Base CSP encoding (base_csp) for the entire belief base
        """
        # self._translation_start_belief_base()
        # for i, conditional in self.epistemic_state.belief_base.conditionals.items():
        #    translated_condtional = Conditional_z3.translate_from_existing(conditional)
        #    self._epistemic_state.conditionals[i] = translated_condtional
        # self.makeCNFs()
        tseitin_transformation = TseitinTransformation(self.epistemic_state)
        tseitin_transformation.belief_base_to_cnf(True, True, True)
        # self._translation_end_belief_base()
        self.compile_constraint(deadline)
        # self._translation_start_belief_base()
        self.base_csp = self.translate()
        # self._translation_end_belief_base()
        # print("Translation done")

    def _inference(
        self, query: Conditional, weakly: bool, deadline: Deadline | None
    ) -> bool:
        """
        Perform c-inference for a single conditional query.

        Implements the core c-inference algorithm by:
        1. Checking for self-fullfilling belief bases (early exit)
        2. Creating query-specific constraints
        3. Solving the combined CSP to determine entailment

        Parameters
        ----------
        query : Conditional
            The conditional query to evaluate for entailment
        weakly : bool
            Whether to use weak consistency (currently unused in c-inference)
        deadline : Deadline or None
            Timeout deadline for the inference operation

        Returns
        -------
        bool
            True if the query is entailed by the belief base, False otherwise

        Notes
        -----
        The algorithm works by checking if the combined CSP (belief base + query
        constraints) is satisfiable. If the CSP is unsatisfiable, the query is
        entailed; if satisfiable, the query is not entailed.

        Self-fullfilling belief bases (where all conditionals are always true)
        are handled as a special case, returning False immediately.
        """
        selffullfilling = True
        for conditional in self.epistemic_state["belief_base"].conditionals.values():
            if is_sat(And(conditional.antecedence, Not(conditional.consequence))):
                selffullfilling = False
        if selffullfilling:
            return False

        # self._translation_start_query()
        # translated_query = Conditional_z3.translate_from_existing(query)
        # self._translation_end_query()
        solver = Solver(name=self.epistemic_state["smt_solver"])
        for constraint in self.base_csp:
            solver.add_assertion(constraint)
            # print(f"new base_csp constraint {constraint}")
        csp, _ = self.compile_and_encode_query(query, deadline)
        for constraint in csp:
            solver.add_assertion(constraint)
            # print(f"new csp constraint {constraint}")
        satcheck = solver.solve()
        # print(f'satcheck {satcheck}')
        return not satcheck

    def compile_constraint(self, deadline: Deadline | None = None) -> float:
        """
        Compile the knowledge base by computing minimal correction subsets.

        This method precomputes the minimal correction subsets for all conditionals
        in the belief base. For each conditional, it determines the smallest sets
        of other conditionals that need to be "corrected" (added/removed) to make
        the conditional consistent with the belief base.

        The results are stored in vMin (verification minima) and fMin (falsification
        minima) dictionaries, which are used during the inference phase.

        Parameters
        ----------
        deadline : Deadline or None, optional
            Timeout deadline for the compilation process. If None, no timeout
            is enforced.

        Returns
        -------
        float
            Execution time in milliseconds for the compilation process

        Notes
        -----
        This is the most computationally expensive part of c-inference preprocessing.
        For each conditional, it solves multiple MaxSAT problems to find minimal
        correction subsets.

        The compilation creates two types of minima:
        - **vMin**: Minimal correction subsets when the conditional is treated as
          a verification constraint (must be true)
        - **fMin**: Minimal correction subsets when the conditional is treated as
          a falsification constraint (must be false)
        """
        start_time = perf_counter_ns() / (1e6)

        for leading_conditional in [
            self.epistemic_state["v_cnf_dict"],
            self.epistemic_state["f_cnf_dict"],
        ]:
            for i, conditional in leading_conditional.items():
                xMins = []
                wcnf = WCNF()
                [wcnf.append(c) for c in conditional]
                [
                    wcnf.append(s, weight=1)
                    for j, softc in self.epistemic_state["nf_cnf_dict"].items()
                    if i != j
                    for s in softc
                ]

                optimizer = create_optimizer(self.epistemic_state)
                xMins_lst = optimizer.minimal_correction_subsets(
                    wcnf, ignore=[i], deadline=deadline
                )

                if leading_conditional is self.epistemic_state["v_cnf_dict"]:
                    self.epistemic_state["vMin"][i] = xMins_lst
                else:
                    self.epistemic_state["fMin"][i] = xMins_lst

        return (perf_counter_ns() / (1e6)) - start_time

    def compile_and_encode_query(
        self, query: Conditional, deadline: Deadline | None = None
    ) -> tuple[list, float]:
        """
        Compile and encode a query for c-inference evaluation.

        This method handles the query-specific part of c-inference by:
        1. Transforming the query into CNF using Tseitin transformation
        2. Computing minimal correction subsets for the query
        3. Encoding the query constraints using minima encoding
        4. Handling edge cases where one side has no correction subsets

        Parameters
        ----------
        query : Conditional
            The conditional query to compile and encode
        deadline : Deadline or None, optional
            Timeout deadline for the compilation process

        Returns
        -------
        tuple[list, float]
            A tuple containing:
            - list of pysmt.FNode: CSP constraints encoding the query
            - float: Execution time in milliseconds

        Notes
        -----
        The method handles several edge cases:
        - **No verification MCS**: Returns empty constraints (not entailed)
        - **No falsification MCS**: Returns impossible constraint (entailed)
        - **Both sides empty**: Returns empty constraints (not entailed)

        The final CSP ensures that verification minima are less than or equal
        to falsification minima for the query to be entailed.

        Examples
        --------
        >>> query = Conditional(q, p, '(q|p)')  # if p then q
        >>> constraints, time = inference.compile_and_encode_query(query)
        >>> print(f"Compiled {len(constraints)} constraints in {time:.2f}ms")
        """
        start_time = perf_counter_ns() / 1e6

        vMin, fMin = [], []
        tseitin_transformation = TseitinTransformation(self.epistemic_state)
        transformed_conditionals = tseitin_transformation.query_to_cnf(query)
        for conditional in transformed_conditionals:
            xMins = []
            wcnf = WCNF()
            [wcnf.append(c) for c in conditional]
            [
                wcnf.append(s, weight=1)
                for j, softc in self.epistemic_state["nf_cnf_dict"].items()
                for s in softc
            ]

            optimizer = create_optimizer(self.epistemic_state)
            xMins_lst = optimizer.minimal_correction_subsets(wcnf, deadline=deadline)

            if conditional is transformed_conditionals[0]:
                vMin = xMins_lst
            else:
                fMin = xMins_lst

        # Short-circuit edge cases where one side has no minimal correction subsets
        if not vMin and fMin:
            # No verification MCS but falsification has MCS -> not entailed
            return [], (perf_counter_ns() / (1e6) - start_time)
        if not fMin and vMin:
            # Verification has MCS but falsification has none -> entailed
            # Return an impossible constraint to force UNSAT when checked
            return [LE(Int(1), Int(0))], (perf_counter_ns() / (1e6) - start_time)
        if not vMin and not fMin:
            # Both sides empty -> default to not entailed
            return [], (perf_counter_ns() / (1e6) - start_time)

        vSum = makeSummation({0: vMin})
        fSum = makeSummation({0: fMin})
        mv, mf = freshVars(0)
        vM = minima_encoding(mv, vSum[0])
        fM = minima_encoding(mf, fSum[0])
        # print(f"vM {vM}")
        # print(f"fM {fM}")
        csp = vM + fM + [GE(mv, mf)]
        # print(f"csp {csp}")
        return csp, (perf_counter_ns() / (1e6) - start_time)
