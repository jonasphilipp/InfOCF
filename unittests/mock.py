import unittest
import unittest.mock

from parser.Wrappers import parse_belief_base, parse_queries


class MockTest(unittest.TestCase):
    """
    fix signatures
    fix empty ckb
    fix queris with unsats, tops, bottoms
    """

    ###mainly parser details, small extensions

    def test(self):
        f1 = "unittests/emptyckb.cl"
        f2 = "unittests/simpleCKB.cl"
        q1 = "unittests/simpleQueries.cl"
        e1 = parse_belief_base(f1)
        print(e1.conditionals)
        print(e1.conditionals)
        e2 = parse_belief_base(f2)
        q = parse_queries(q1)
        print(e2.conditionals)
        print(q.conditionals)
