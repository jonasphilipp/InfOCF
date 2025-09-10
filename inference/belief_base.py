"""
Belief Base Representations

This module provides classes for representing conditional belief bases, which are
collections of conditional statements that form the knowledge base for non-monotonic
inference operations.
"""

# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------

from inference.conditional import Conditional


class BeliefBase:
    """
    Represents a conditional belief base containing a set of conditional statements.

    A belief base is a finite set of conditionals that represent the agent's knowledge
    or beliefs about the domain. Each conditional is of the form (B|A), meaning
    "if A then usually B". The belief base serves as the foundation for various inference
    operations in conditional logic.


    Parameters
    ----------
    signature : list of str
        List of propositional variable names that can appear in the conditionals.
        These define the domain of discourse for the belief base.
    conditionals : dict[int, Conditional]
        Dictionary mapping integer indices to Conditional objects.
        The keys serve as unique identifiers for the conditionals.
    name : str
        Human-readable name for this belief base, used for identification
        and debugging purposes.

    Attributes
    ----------
    signature : list of str
        The propositional signature (domain variables)
    conditionals : dict[int, Conditional]
        The conditional statements indexed by integer keys
    name : str
        The name of this belief base

    Examples
    --------
    >>> from parser.Wrappers import parse_belief_base
    >>>
    >>> # Parse belief base from string (recommended approach)
    >>> belief_base_str = '''
    ... signature
    ...   p, q, r
    ... conditionals
    ... example{
    ...   (q|p),
    ...   (r|q)
    ... }
    ... '''
    >>> bb = parse_belief_base(belief_base_str)
    >>> print(f"Parsed belief base '{bb.name}' with {len(bb.conditionals)} conditionals")
    >>>
    >>> # Or parse from file
    >>> # bb = parse_belief_base("path/to/belief_base.ckb")

    Manual construction (for advanced users):

    >>> from inference.conditional import Conditional
    >>> from pysmt.shortcuts import Symbol
    >>>
    >>> # Create some propositional variables
    >>> p = Symbol('p')
    >>> q = Symbol('q')
    >>> r = Symbol('r')
    >>>
    >>> # Define signature
    >>> signature = ['p', 'q', 'r']
    >>>
    >>> # Create conditionals
    >>> cond1 = Conditional(q, p, '(q|p)')  # if p then q
    >>> cond2 = Conditional(r, q, '(r|q)')  # if q then r
    >>>
    >>> # Create belief base
    >>> conditionals = {0: cond1, 1: cond2}
    >>> bb = BeliefBase(signature, conditionals, 'example_bb')
    >>>
    >>> print(f"Belief base '{bb.name}' has {len(bb.conditionals)} conditionals")

    Notes
    -----
    The belief base representation is central to all inference operations in InfOCF.
    Different inference operators (p-entailment, system Z, system W, c-inference)
    interpret the same belief base in different ways to produce different entailment
    relations.
    """

    def __init__(
        self, signature: list[str], conditionals: dict[int, Conditional], name: str
    ) -> None:
        """
        Initialize a conditional belief base.

        Parameters
        ----------
        signature : list of str
            List of propositional variable names in the domain
        conditionals : dict[int, Conditional]
            Dictionary of conditionals indexed by integers
        name : str
            Human-readable name for the belief base
        """
        self.signature = signature
        self.conditionals = conditionals
        self.name = name
