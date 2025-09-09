# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------

import logging
from abc import ABC, abstractmethod
from time import perf_counter

# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------
from typing import cast

from pysat.card import IDPool
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------
from infocf.log_setup import get_logger

logger = get_logger(__name__)


class Optimizer(ABC):
    epistemic_state: dict[str, object]

    """
    Initializes Optimizer (pmaxsat solver) object and creates needed dict entries if not present.

    Context:
        Called beforer pmaxsat solver delivers minimal corretion subsets

    Parameters:
        epistemic_state dict

    Side Effects:
        pool, v_cnf_dict, f_cnf_dict, nf_cnf_dict entries in epistemic_state
    """

    def __init__(self, epistemic_state: dict[str, object]):
        if "pool" not in epistemic_state:
            epistemic_state["pool"] = IDPool()
        if "v_cnf_dict" not in epistemic_state:
            epistemic_state["v_cnf_dict"] = dict()
        if "f_cnf_dict" not in epistemic_state:
            epistemic_state["f_cnf_dict"] = dict()
        if "nf_cnf_dict" not in epistemic_state:
            epistemic_state["nf_cnf_dict"] = dict()

        self.epistemic_state = epistemic_state

    """
    abstraction of method returning minimal correction subsets

    Context:
        called by system-w and c-inference to get minimal correction subsets by using
        pmaxsat solver

    Parameters:
        wcnf object (weighted partial maxsat; see pysat for details), and index of nf_cnf in
        nf_cnf_dict to be ignored if desired (typically desired for internals of c-inference)

    Returns:
        minimal correction subsets of indices negated falsifications of conditionals

    """

    @abstractmethod
    def minimal_correction_subsets(
        self, wcnf: WCNF, ignore: list[int] = []
    ) -> list[list[int]]:
        return []

    """
    Takes model and returns all IDs of CNFs in notAorBs (i.e. Not(A, Not(B))) that are not satisfied
    by the model

    Context:
        Helper function called by compile_constraint and compile_and_encode_query

    Parameters:
        RC2 model; cost of the model; ID of CNF in notAorBs to be ignored (important to implement
        the 'i!=j, AB[i]/notAB[i], notAorB[j]' requirement in compile_constraint)

    Returns:
        Set of IDs
    """

    def get_violated_conditional(
        self, model: list[int], cost: int, ignore: list[int]
    ) -> set[int]:
        violated: set[int] = set()
        if cost > 0:
            counter = 0
            nf_cnf_dict = cast(
                dict[int, list[list[int]]], self.epistemic_state["nf_cnf_dict"]
            )  # type: ignore[assignment]
            for index, conditional in nf_cnf_dict.items():
                if index in ignore:
                    continue
                for clause in conditional:
                    if not any(x in clause for x in model):
                        counter += 1
                        violated.add(index)
                    if counter == cost:
                        return violated
        return violated

    """
    Takes indices of violated CNFs and creates new CNF that can be added as hard constraint to the
    solver. Based on the idea of restraining the solver from violating the same conjuction of CNFs
    again.

    Context:
        Helper function called by compile_constraint in order to add new hard constraint to solver
        and make solver solve for different possible world

    Parameters:
        set of indices of unsatisfied CNFs in notAorBs

    Returns:
        int CNF equivalent to disjunction of all CNFs referred to by input indices
    """

    def exclude_violated(self, violated: set[int]) -> list[list[int]]:
        return_constraints: list[list[int]] = []
        helper_variables_clause: list[int] = []

        pool = cast(IDPool, self.epistemic_state["pool"])  # type: ignore[assignment]
        nf_cnf_dict = cast(
            dict[int, list[list[int]]], self.epistemic_state["nf_cnf_dict"]
        )  # type: ignore[assignment]

        for index in violated:
            hid = pool.id(index)
            for clause in nf_cnf_dict[index]:
                new_clause = clause[:]
                new_clause.append(hid * (-1))
                return_constraints.append(new_clause)

            helper_variables_clause.append(hid)
        return_constraints.append(helper_variables_clause)
        return return_constraints


"""
Removes supersets and converts sets to lists

Context:
    Helper function called by compile_constraint

Parameters:
    list of sets (some sets might be supersets of other sets)

Returns:
    lists of lists (none of the inner lists will be a superset of other inner list)
"""


def remove_supersets(lst_of_sets: list[set[int]]) -> list[list[int]]:
    lst_of_sets = sorted(lst_of_sets, key=len)
    filtered = []

    for a in lst_of_sets:
        is_superset = False
        for b in filtered:
            if b.issubset(a):
                is_superset = True
                break
        if not is_superset:
            filtered.append(a)

    return [list(s) for s in filtered]


class OptimizerRC2(Optimizer):
    """
    RC2 based implementation of Optimizer (partial maxsat solver)
    """

    def minimal_correction_subsets(
        self, wcnf: WCNF, ignore: list[int] = []
    ) -> list[list[int]]:
        xMins: list[set[int]] = []
        sat_solver = str(self.epistemic_state.get("pmaxsat_solver", ""))[4:]
        if not sat_solver:
            sat_solver = "g3"
        model_count = 0
        with RC2(wcnf, solver=sat_solver) as rc2:
            while True:
                kill_time_val = float(self.epistemic_state.get("kill_time", 0) or 0)
                if kill_time_val and perf_counter() > kill_time_val:
                    raise TimeoutError

                model = rc2.compute()

                if model is None:
                    if logger.isEnabledFor(logging.DEBUG):
                        logger.debug("models found: %s", model_count)
                    break
                model_count += 1
                cost = rc2.cost

                violated = self.get_violated_conditional(model, cost, ignore)

                if not violated:
                    xMins.append(violated)
                    break

                xMins.append(violated)
                clauses_to_add = self.exclude_violated(violated)

                [rc2.add_clause(clause) for clause in clauses_to_add]

        xMins_lst: list[list[int]] = remove_supersets(xMins)
        return xMins_lst


"""
creates instanciation of optimizer. gratuitous since only one child class implements 'optimizer'
right now but implementation of additional partial maxsat solvers planned

Context:
    called whenever (rc2) pmaxsat solver is needed (by system-w or c-inference)

Parameters:
    epistemic_state

Returns:
    the solver
"""


def create_optimizer(epistemic_state: dict[str, object]) -> Optimizer:
    solver_name = str(epistemic_state.get("pmaxsat_solver", ""))
    if solver_name.startswith("rc2"):
        optimizer: Optimizer = OptimizerRC2(epistemic_state)
        return optimizer
    raise ValueError("no correct optimizer provided")
