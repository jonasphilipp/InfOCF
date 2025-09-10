"""
Conditional Logic Representations

This module provides classes and utilities for representing conditional statements
in conditional logic. Conditionals are fundamental building blocks for belief bases
and inference operations in non-monotonic reasoning systems.
"""

# ---------------------------------------------------------------------------
# Standard library
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Third-party
# ---------------------------------------------------------------------------

from pysmt.shortcuts import And, Not, Or

# ---------------------------------------------------------------------------
# Project modules
# ---------------------------------------------------------------------------


class Conditional:
    """
    Represents a conditional statement of the form (B|A), meaning "if A then usually B".

    Parameters
    ----------
    consequence : pysmt.FNode
        The consequent formula B in the conditional (B|A)
    antecedence : pysmt.FNode
        The antecedent formula A in the conditional (B|A)
    textRepresentation : str
        String representation of the conditional, typically in format "(B|A)"
    weak : bool, optional
        Whether this is a weak conditional (default: False)

    Attributes
    ----------
    antecedence : pysmt.FNode
        The antecedent formula A
    consequence : pysmt.FNode
        The consequent formula B
    weak : bool
        Whether this is a weak conditional
    textRepresentation : str
        String representation of the conditional
    index : int or None
        Optional external identifier used as keys in belief bases
    consequenceText : str
        Text representation of the consequence (set by setTexts())
    antecedenceText : str
        Text representation of the antecedence (set by setTexts())
    consequenceVars : set of str
        Set of variable names in the consequence (set by setTexts())
    antecedenceVars : set of str
        Set of variable names in the antecedence (set by setTexts())

    Examples
    --------
    >>> from parser.Wrappers import parse_formula
    >>>
    >>> # Parse conditional from string (recommended approach)
    >>> antecedent = parse_formula('p')    # A = p
    >>> consequent = parse_formula('q')    # B = q
    >>> cond = Conditional(consequent, antecedent, '(q|p)')  # represents "if p then q"
    >>> print(cond)
    (q|p)
    >>>
    >>> # Or with more complex formulas
    >>> ant = parse_formula('p, r')        # A = p ∧ r
    >>> cons = parse_formula('q; s')       # B = q ∨ s
    >>> cond2 = Conditional(cons, ant, '(q;s|p,r)')
    >>> print(cond2)
    (q;s|p,r)

    Manual construction with PySMT symbols (for advanced users):

    >>> from pysmt.shortcuts import Symbol
    >>> p = Symbol('p')
    >>> q = Symbol('q')
    >>> cond = Conditional(q, p, '(q|p)')  # represents "if p then q"
    >>> print(cond)
    (q|p)
    """

    def __init__(self, consequence, antecedence, textRepresentation, weak=False):
        """
        Initialize a conditional statement.

        Parameters
        ----------
        consequence : pysmt.FNode
            The consequent formula B
        antecedence : pysmt.FNode
            The antecedent formula A
        textRepresentation : str
            String representation of the conditional
        weak : bool, optional
            Whether this is a weak conditional (default: False)
        """
        self.antecedence = antecedence
        self.consequence = consequence
        self.weak = weak
        self.textRepresentation = textRepresentation
        # Optional external identifier used across the codebase (e.g., as keys
        # in belief bases or intermediate structures). Some callers set it
        # explicitly; others leave it unset.
        self.index: int | None = None

    def make_A_then_B(self):
        """
        Create the logical formula A ∧ B (antecedence and consequence).

        Returns
        -------
        pysmt.FNode
            Logical conjunction of antecedence and consequence

        Examples
        --------
        >>> from pysmt.shortcuts import Symbol
        >>> p, q = Symbol('p'), Symbol('q')
        >>> cond = Conditional(q, p, '(q|p)')
        >>> formula = cond.make_A_then_B()  # equivalent to p ∧ q
        """
        return And(self.antecedence, self.consequence)

    def setTexts(self, consequenceText, antecedenceText):
        """
        Set text representations and extract variable names.

        This method stores human-readable text representations of the formulas
        and extracts the variable names used in each part.

        Parameters
        ----------
        consequenceText : str
            Text representation of the consequence
        antecedenceText : str
            Text representation of the antecedence

        Notes
        -----
        After calling this method, the following attributes are available:
        - consequenceText: text representation of consequence
        - antecedenceText: text representation of antecedence
        - consequenceVars: set of variable names in consequence
        - antecedenceVars: set of variable names in antecedence
        """
        self.consequenceText = consequenceText
        self.antecedenceText = antecedenceText
        self.consequenceVars = set(str.split(self.consequenceText.translate(a)))  # type: ignore
        self.antecedenceVars = set(str.split(self.antecedenceText.translate(a)))  # type: ignore

    def make_A_then_not_B(self):
        """
        Create the logical formula A ∧ ¬B (antecedence and negation of consequence).

        This is used in inference algorithms to check for counterexamples.

        Returns
        -------
        pysmt.FNode
            Logical conjunction of antecedence and negated consequence

        Examples
        --------
        >>> from pysmt.shortcuts import Symbol
        >>> p, q = Symbol('p'), Symbol('q')
        >>> cond = Conditional(q, p, '(q|p)')
        >>> formula = cond.make_A_then_not_B()  # equivalent to p ∧ ¬q
        """
        return And(self.antecedence, Not(self.consequence))

    def make_B(self):
        """
        Return just the consequence formula.

        Returns
        -------
        pysmt.FNode
            The consequence formula B
        """
        return self.consequence

    def make_not_A_or_B(self):
        """
        Create the logical formula ¬A ∨ B (material implication form).

        This is the standard logical equivalent of the conditional A → B.

        Returns
        -------
        pysmt.FNode
            Logical disjunction of negated antecedence and consequence

        Examples
        --------
        >>> from pysmt.shortcuts import Symbol
        >>> p, q = Symbol('p'), Symbol('q')
        >>> cond = Conditional(q, p, '(q|p)')
        >>> formula = cond.make_not_A_or_B()  # equivalent to ¬p ∨ q
        """
        return Or(Not(self.antecedence), self.consequence)

    def __str__(self):
        """
        Return string representation of the conditional.

        Returns
        -------
        str
            The text representation of the conditional
        """
        return self.textRepresentation

    def __repr__(self):
        """
        Return detailed string representation of the conditional.

        Returns
        -------
        str
            The text representation of the conditional (same as __str__)
        """
        return self.textRepresentation
