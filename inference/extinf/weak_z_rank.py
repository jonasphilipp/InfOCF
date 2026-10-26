from inference.extinf.weaklexinf import LexInf
from inference.z3tools import transform_conditional_to_z3


def index_nz(x):
    if len(x) == 0:
        return 0
    if x[0] != 0:
        return 1
    if x[0] == 0:
        return 1 + index_nz(x[1:])


class SystemZRank:
    def __init__(self, bb) -> None:
        self.lexinf = LexInf(bb)

    def rank(self, formula):
        reg = self.lexinf.rank(formula)
        if all([x == 0 for x in reg]):
            return 0
        if reg[0] > 0:
            return float("inf")
        return len(reg) - index_nz(reg) + 1

    def rank_query(self, query):
        query = transform_conditional_to_z3(query)
        vf = query.verify()
        ff = query.falsify()
        return self.rank(vf), self.rank(ff)
