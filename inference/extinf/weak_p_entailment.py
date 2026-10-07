
from pysmt.shortcuts import Not

from inference.belief_base import BeliefBase
from inference.conditional import Conditional
from inference.extinf.weak_z_rank import SystemZRank
from inference.extinf.z3tools import transform_conditional_to_z3


class ExtendedPEntailment():
    ## TODO refactor to use lexinf

    def __init__(self,bb) -> None:
        self.bb = bb



    def rank_query(self, query):
        tmp = {i:c for i,c in self.bb.conditionals.items()}
        tmpConditional = Conditional(Not(query.B), query.A, "", "")
        tmp[len(tmp)+1]=tmpConditional
        kappaz = SystemZRank(BeliefBase("",tmp,""))
        query = transform_conditional_to_z3(query)
        return kappaz.rank(query.A) == float('inf')


    def inference(self, query):
        return self.rank_query(query)







