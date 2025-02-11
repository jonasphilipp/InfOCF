from time import time_ns
from pysmt.shortcuts import Symbol, Int, LE, GE, And, Plus, Not,  is_unsat, Solver, LT, INT, GT
from pysat.formula import WCNF
from inference.inference import Inference
from inference.conditional import Conditional
from inference.tseitin_transformation import TseitinTransformation
from inference.optimizer import create_optimizer
from inference.consistency_sat import checkTautologies

### some cleanup and some more documentation of class' funcitonalities pending


class CInference(Inference):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        if 'vMin' not in self.epistemic_state:
            self.epistemic_state['vMin'] = dict()
        if 'fMin' not in self.epistemic_state:
            self.epistemic_state['fMin'] = dict()

    #replaces every items in the argument by it's sum representation
    def makeSummation(self, minima: dict) -> dict[int, list]:
        results = dict()
        for index, summ in minima.items():
            interim = []
            for subsum in summ:
                if subsum:
                    interim.append(Plus([Symbol(f'eta_{i}', INT) for i in subsum]))
                else:
                    interim.append(Int(0))  # Or use 0 directly
            results[index] = interim
        return results

    def freshVars(self, i: int) -> tuple:
        return Symbol(f'mv_{i}', INT), Symbol(f'mf_{i}', INT)

    def minima_encoding(self, mv: int, ssums: list) -> list:
        ands = [LE(mv, i) for i in ssums]
        ors = Not(And([LT(mv, i) for i in ssums]))
        ands.append(ors)
        return ands

    def encoding(self, etas: dict, vSums: dict, fSums: dict) -> list:
        csp = []
        for index, eta in etas.items():
            mv, mf = self.freshVars(index)
            vMin = self.minima_encoding(mv, vSums[index])
            fMin = self.minima_encoding(mf, fSums[index])
            csp.extend(vMin)
            csp.extend(fMin)
            csp.append(GT(eta, mv - mf))
        return csp

    def translate(self) -> list:
        eta = {i: Symbol(f'eta_{i}', INT) for i, _ in enumerate(self.epistemic_state['belief_base'].conditionals, start=1)}
        #defeat= = checkTautologies(self.epistemic_state['belief_base'].conditionals)
        #if not defeat: return False
        gteZeros = [GE(e, Int(0)) for e in eta.values()]
        vSums = self.makeSummation(self.epistemic_state['vMin'])
        fSums = self.makeSummation(self.epistemic_state['fMin'])
        csp = self.encoding(eta, vSums, fSums)
        csp.extend(gteZeros)
        return csp


    



    def _preprocess_belief_base(self) -> None:
        #self._translation_start_belief_base()
        #for i, conditional in self.epistemic_state.belief_base.conditionals.items():
        #    translated_condtional = Conditional_z3.translate_from_existing(conditional)
        #    self._epistemic_state.conditionals[i] = translated_condtional
        #self.makeCNFs()
        tseitin_transformation = TseitinTransformation(self.epistemic_state)
        tseitin_transformation.belief_base_to_cnf(True, True, True)
        #self._translation_end_belief_base()
        self.compile_constraint()
        #self._translation_start_belief_base()
        self.base_csp = self.translate()
        #self._translation_end_belief_base()
        #print("Translation done")




    def _inference(self, query: Conditional) -> bool:
        ql,qr=2 * [is_unsat(query.antecedencexi,query.consequence)]
        defeat = len(self.epistemic_state['belief_base'].conditionals)
        if defeat==0: return ql,qr
        if ql: return True
        if qr: return False
        #self._translation_start_query()
        #translated_query = Conditional_z3.translate_from_existing(query)
        #self._translation_end_query()
        solver = Solver(name=self.epistemic_state['smt_solver'])
        for constraint in self.base_csp:
            solver.add_assertion(constraint)
            #print(f"new base_csp constraint {constraint}")
        csp, _ = self.compile_and_encode_query(query)
        for constraint in csp:
            solver.add_assertion(constraint)
            #print(f"new csp constraint {constraint}")
        satcheck = solver.solve()
        #print(f'satcheck {satcheck}')
        return not satcheck


    """
    Compiles KB by filling the dicts vMin and fMin with lists of lists of ints. Each inner list 
    corresponds to a possible world while the ints represent indices in notAorBs of unsatisfied CNFs. 
    The index of vMin/fMin equals the index of the CNF in ABs/notABs that has been used as a hard
    constrain before checking what CNFs in notAorBs can be satisfied in different possible worlds.

    Context:
        This Method is called to compile a KB based on conditionals in self.conditionals

    Returns:
        Execution time in ms
    """
    def compile_constraint(self) -> float:
        start_time = time_ns() / (1e+6)

        for leading_conditional in [self.epistemic_state['v_cnf_dict'], self.epistemic_state['f_cnf_dict']]:
            for i, conditional in leading_conditional.items():
                xMins = []
                wcnf = WCNF()
                [wcnf.append(c) for c in conditional]
                [wcnf.append(s, weight=1) for j, softc in self.epistemic_state['nf_cnf_dict'].items() if i != j for s in softc]
                
                optimizer = create_optimizer(self.epistemic_state)
                xMins_lst = optimizer.minimal_correction_subsets(wcnf, i)

                if leading_conditional is self.epistemic_state['v_cnf_dict']:
                    self.epistemic_state['vMin'][i] = xMins_lst
                else: 
                    self.epistemic_state['fMin'][i] = xMins_lst

        return (time_ns()/(1e+6))-start_time
    

    """
    Compiles query using RC2 and encodes it using minima_encoding.

    Context:
        This method is used to query the KB and do actual inference.

    Parameters:
        The Query in form of a conditional

    Returns:
        Constraint satisfaction problem that can be fed into the z3 solver;
        Execution time
    """
    def compile_and_encode_query(self, query: Conditional) -> tuple[list, float]:
        start_time = time_ns() / 1e+6

        vMin, fMin = [], []
        tseitin_transformation = TseitinTransformation(self.epistemic_state)
        transformed_conditionals = tseitin_transformation.query_to_cnf(query)
        for conditional in transformed_conditionals:
            xMins = []
            wcnf = WCNF()
            [wcnf.append(c) for c in conditional]
            [wcnf.append(s, weight=1) for j, softc in self.epistemic_state['nf_cnf_dict'].items() for s in softc]
            
            optimizer = create_optimizer(self.epistemic_state)
            xMins_lst = optimizer.minimal_correction_subsets(wcnf)

            if conditional is transformed_conditionals[0]:
                vMin = xMins_lst
            else: 
                fMin = xMins_lst

        vSum = self.makeSummation({0:vMin})
        fSum = self.makeSummation({0:fMin})
        mv, mf = self.freshVars(0)
        vM = self.minima_encoding(mv, vSum[0])
        fM = self.minima_encoding(mf, fSum[0])
        #print(f"vM {vM}")
        #print(f"fM {fM}")
        csp = vM + fM + [GE(mv, mf)]
        #print(f"csp {csp}")
        return csp ,(time_ns()/(1e+6)-start_time)

