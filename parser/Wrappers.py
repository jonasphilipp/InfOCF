"""
Parser Wrappers for Conditional Knowledge Bases

This module provides high-level wrapper functions for parsing conditional knowledge bases,
queries, and propositional formulas using ANTLR4-based parsers. It serves as the main
interface between the InfOCF library and the underlying parsing infrastructure.

The module supports parsing of:
- Conditional belief bases in .cl format
- Query files in .clq format
- Individual propositional formulas
- Error handling and reporting

The parsing is based on the Conditional Logic Knowledge Representation (CLKR) format,
which uses a structured syntax for representing conditional statements and belief bases.
"""

import logging
import os

from antlr4 import CommonTokenStream, InputStream
from antlr4.error.ErrorListener import ErrorListener

from inference.belief_base import BeliefBase

# from .QUERYLexer import QUERYLexer
# from .QUERYParser import QUERYParser
# from .myQueryVisitor import myQueryVisitor
from inference.queries import Queries
from infocf.log_setup import get_logger

from .CKBLexer import CKBLexer
from .CKBParser import CKBParser
from .myVisitor import myVisitor

logger = get_logger(__name__)


# ============================================================================
# Public API Functions
# ============================================================================

# Public API functions continue below...


def parse_belief_base(string: str) -> BeliefBase:
    """
    Parse a belief base from a file path or string content.

    This is a convenience function that automatically detects whether the input
    is a file path or direct string content, and parses it accordingly.

    Parameters
    ----------
    string : str
        Either a file path to a .cl file or the string content of a belief base
        in CLKR format

    Returns
    -------
    BeliefBase
        The parsed belief base object containing the signature and conditionals

    Raises
    ------
    Exception
        If parsing fails due to syntax errors in the input
    FileNotFoundError
        If the specified file path does not exist

    Examples
    --------
    >>> # Parse from file
    >>> bb = parse_belief_base('example.cl')
    >>>
    >>> # Parse from string
    >>> content = '''
    ... signature
    ...   p, q, r
    ... conditionals
    ... example{
    ...   (p|q),
    ...   (q|r)
    ... }
    ... '''
    >>> bb = parse_belief_base(content)

    See Also
    --------
    parseCKB : Core parsing function
    BeliefBase : The resulting belief base object
    """
    if os.path.isfile(string):
        with open(string) as f:
            file = f.read()
        belief_base = parseCKB(file)
    else:
        belief_base = parseCKB(string)
    return belief_base


def parse_queries(string: str) -> Queries:
    """
    Parse queries from a file path or string content.

    This function automatically detects whether the input is a file path or
    direct string content and parses it as a set of conditional queries.

    Parameters
    ----------
    string : str
        Either a file path to a .clq file or the string content containing
        conditional queries

    Returns
    -------
    Queries
        A Queries object containing the parsed conditional queries

    Raises
    ------
    Exception
        If parsing fails due to syntax errors in the input
    FileNotFoundError
        If the specified file path does not exist

    Examples
    --------
    >>> # Parse from file
    >>> queries = parse_queries('queries.clq')
    >>>
    >>> # Parse from string
    >>> query_str = '(p|q), (q|r)'
    >>> queries = parse_queries(query_str)

    See Also
    --------
    parse_queries_from_str : Core query parsing function
    Queries : The resulting queries object
    """
    if os.path.isfile(string):
        with open(string) as f:
            file = f.read()
        queries = parse_queries_from_str(file)
    else:
        queries = parse_queries_from_str(string)
    return queries


def parse_queries_from_str(string: str) -> Queries:
    """
    Parse queries from a string, handling both full belief bases and simple queries.

    This function can handle two types of input:
    1. Full belief base format with signature and conditionals sections
    2. Simple list of conditional queries

    Parameters
    ----------
    string : str
        String containing either a full belief base or a list of conditional queries

    Returns
    -------
    Queries
        A Queries object containing the parsed conditional queries

    Raises
    ------
    Exception
        If parsing fails due to syntax errors in the input

    Notes
    -----
    The function uses a heuristic to detect the input format:
    - If the string contains both "signature" and "conditionals", it's treated as a full belief base
    - Otherwise, it's treated as a simple list of queries

    For simple queries, a dummy belief base template is created internally.

    Examples
    --------
    >>> # Parse full belief base format
    >>> full_format = '''
    ... signature
    ...   p, q, r
    ... conditionals
    ... queries{
    ...   (p|q),
    ...   (q|r)
    ... }
    ... '''
    >>> queries = parse_queries_from_str(full_format)
    >>>
    >>> # Parse simple query list
    >>> simple_queries = '(p|q), (q|r), (r|p)'
    >>> queries = parse_queries_from_str(simple_queries)

    See Also
    --------
    parseQuery : Helper function for simple query parsing
    parseCKB : Function for parsing full belief bases
    Queries : The resulting queries container
    """
    if "signature" and "conditionals" in string:
        belief_base = parseCKB(string)
        queries = Queries(belief_base)
    else:
        query_dict = parseQuery(string)
        if query_dict:
            queries = Queries(query_dict)
    return queries  # type: ignore


def parse_belief_base_from_str(string: str):
    """
    Parse a belief base from a string (alias for parseCKB).

    This is a simple alias function for parseCKB for consistency with
    the naming convention used in other parsing functions.

    Parameters
    ----------
    string : str
        The belief base string in CLKR format

    Returns
    -------
    BeliefBase
        The parsed belief base object

    See Also
    --------
    parseCKB : The underlying parsing function
    parse_belief_base : More flexible function that handles files or strings
    """
    return parseCKB(string)


def parseCKB(ckbs_string):
    """
    Parse a Conditional Knowledge Base (CKB) string into a BeliefBase object.

    This is the core parsing function that converts CLKR-formatted strings
    into BeliefBase objects. It uses the ANTLR4 parser infrastructure to
    perform lexical analysis, parsing, and AST construction.

    Parameters
    ----------
    ckbs_string : str
        The conditional knowledge base string in CLKR format, containing:
        - A signature section listing propositional variables
        - A conditionals section with conditional statements

    Returns
    -------
    BeliefBase
        A BeliefBase object containing the parsed signature and conditionals

    Raises
    ------
    Exception
        If parsing fails due to syntax errors, with detailed line and column information

    Notes
    -----
    The parsing process involves:
    1. Parse tree construction using internal parsing pipeline
    2. AST traversal using myVisitor() to extract structured data
    3. BeliefBase object construction from the parsed components

    The function expects input in the CLKR format:
    ```
    signature
      var1, var2, var3
    conditionals
    kb_name{
      (condition|consequence),
      (condition2|consequence2)
    }
    ```

    Examples
    --------
    >>> ckb_str = '''
    ... signature
    ...   p, q, r
    ... conditionals
    ... example{
    ...   (p|q),
    ...   (q|r)
    ... }
    ... '''
    >>> belief_base = parseCKB(ckb_str)
    >>> print(f"Parsed {len(belief_base.conditionals)} conditionals")

    See Also
    --------
    myVisitor : AST visitor for extracting structured data
    BeliefBase : The resulting belief base container
    """
    if logger.isEnabledFor(logging.DEBUG):
        logger.debug(
            "Parsing CKB string: %s",
            ckbs_string[:100] + "..." if len(ckbs_string) > 100 else ckbs_string,
        )
    tree = _getParseTree(ckbs_string)
    visitor = myVisitor()
    ckbs = visitor.visit(tree)
    ckb = list(ckbs.values())[0]
    return ckb


def parseQuery(querystring):
    """
    Parse a simple query string into a conditionals dictionary.

    This function handles simple conditional queries that don't have a full
    belief base structure. It creates a minimal template belief base internally
    and extracts just the conditionals dictionary.

    Parameters
    ----------
    querystring : str
        String containing conditional queries, e.g., "(p|q), (q|r)"

    Returns
    -------
    dict[int, Conditional]
        Dictionary mapping integer indices to Conditional objects

    Raises
    ------
    Exception
        If parsing fails due to syntax errors in the query string

    Notes
    -----
    The function creates a dummy belief base with a fixed signature (a,b,c,d,e,f)
    and wraps the query string in the required CLKR format. This allows simple
    queries to be parsed without requiring the full belief base structure.

    The dummy signature is sufficient for most use cases since the actual
    variable names are preserved in the conditional objects themselves.

    Examples
    --------
    >>> query_str = "(p|q), (q|r), (r|p)"
    >>> conditionals = parseQuery(query_str)
    >>> print(f"Parsed {len(conditionals)} conditionals")

    See Also
    --------
    parseCKB : Full belief base parsing
    parse_queries_from_str : Higher-level query parsing function
    """
    ckb_template = f"signature \n a,b,c,d,e,f \n conditionals \n Querydummy \n {{ \n {querystring}\n }}"
    ckbquery = parseCKB(ckb_template)
    if logger.isEnabledFor(logging.DEBUG):
        logger.debug("Parsed query: %s", ckbquery.conditionals)
    # query.__class__ = Queries
    return ckbquery.conditionals


def parse_formula(string: str):
    """
    Parse a propositional formula using the CKB grammar and return a PySMT formula.

    This function parses individual propositional formulas using the same grammar
    as the belief base parser. It supports the native CLKR syntax for logical
    operators and returns PySMT formula objects that can be used with SMT solvers.

    Parameters
    ----------
    string : str
        The propositional formula string using CLKR syntax:
        - `!` for negation (e.g., `!p`)
        - `,` for conjunction (AND) (e.g., `p, q`)
        - `;` for disjunction (OR) (e.g., `p; q`)
        - Parentheses for grouping (e.g., `(p; q), r`)

    Returns
    -------
    pysmt.FNode
        A PySMT formula object representing the parsed logical expression

    Raises
    ------
    Exception
        If parsing fails due to syntax errors in the formula
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        raise Exception(f"Syntax error at line {line}, column {column}: {msg}")
    -----
    The function uses the CKB grammar's formula rule to parse expressions.
    Variables are automatically recorded during parsing and can be accessed
    through the visitor's sigcheck attribute.

    The resulting PySMT formula can be used with InfOCF's inference operators
    or directly with PySMT's solver interface.

    Examples
    --------
    >>> # Parse a simple conjunction
    >>> formula = parse_formula("p, q")
    >>>
    >>> # Parse a more complex formula
    >>> formula = parse_formula("(p; q), !r")
    >>>
    >>> # Parse a single variable
    >>> formula = parse_formula("p")

    See Also
    --------
    CKBLexer : The lexer for the CKB grammar
    CKBParser : The parser for the CKB grammar
    myVisitor : AST visitor that converts parse trees to PySMT formulas
    """
    # Use the grammar's native syntax directly
    s = string

    # Setup parser with error listeners
    stream = InputStream(s)
    lexer = CKBLexer(stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(_ThrowingErrorListener())
    tokens = CommonTokenStream(lexer)
    parser = CKBParser(tokens)
    parser.removeErrorListeners()
    parser.addErrorListener(_ThrowingErrorListener())

    # Parse formula rule
    tree = parser.formula()
    visitor = myVisitor()
    # Initialize sigcheck so visitVar can record variables without attribute errors
    visitor.sigcheck = []
    return visitor.visit(tree)


# ============================================================================
# Internal Implementation Functions and Classes
# ============================================================================


def _getParseTree(ckbs_string):
    """
    Parse a CKB string and return the ANTLR4 parse tree.

    This function performs the complete parsing pipeline from string input
    to parse tree, including lexical analysis, tokenization, and parsing.
    It uses strict error handling that raises exceptions on any parsing errors.

    This is an internal utility function used by higher-level parsing functions.
    Most users should use parse_belief_base() or parseCKB() instead.

    Parameters
    ----------
    ckbs_string : str
        The conditional knowledge base string to parse, following the CLKR format

    Returns
    -------
    antlr4.tree.Tree
        The ANTLR4 parse tree representing the parsed structure

    Raises
    ------
    Exception
        If any syntax errors are encountered during parsing, with detailed
        line and column information

    Notes
    -----
    The parsing process involves:
    1. Creating an InputStream from the string
    2. Lexical analysis using CKBLexer
    3. Tokenization using CommonTokenStream
    4. Syntactic parsing using CKBParser
    5. Error handling via _ThrowingErrorListener
    """
    stream = InputStream(ckbs_string)
    lexer = CKBLexer(stream)
    lexer.removeErrorListeners()
    lexer.addErrorListener(_ThrowingErrorListener())

    stream = CommonTokenStream(lexer)
    parser = CKBParser(stream)
    parser.removeErrorListeners()
    parser.addErrorListener(_ThrowingErrorListener())

    tree = parser.ckbs()
    return tree


class _ThrowingErrorListener(ErrorListener):
    """
    ANTLR4 error listener that converts parsing errors into Python exceptions.

    This class extends ANTLR4's ErrorListener to provide strict error handling
    during parsing. Instead of logging parsing errors, it raises exceptions
    that can be caught and handled by calling code.

    This ensures that parsing failures are not silently ignored and provides
    clear error messages with line and column information.

    Note: This is an internal implementation class and not part of the public API.

    Attributes
    ----------
    Inherits all attributes from antlr4.error.ErrorListener.ErrorListener
    """

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        """
        Handle syntax errors by raising an exception with detailed error information.

        Parameters
        ----------
        recognizer : antlr4.Parser
            The parser that detected the error
        offendingSymbol : antlr4.Token
            The token that caused the error
        line : int
            Line number where the error occurred
        column : int
            Column number where the error occurred
        msg : str
            Error message describing the parsing failure
        e : antlr4.RecognitionException
            The recognition exception that was raised

        Raises
        ------
        Exception
            Always raises an exception with formatted error message including
            line and column information
        """
        raise Exception(f"Syntax error at line {line}, column {column}: {msg}")
