from time import time_ns
from pysmt.shortcuts import Symbol, Int, LE, GE, And, Plus, Not, is_sat, is_unsat, Solver, LT, INT, GT, Implies
from pysat.formula import WCNF
from inference.inference import Inference
from inference.conditional import Conditional
from inference.tseitin_transformation import TseitinTransformation
from inference.optimizer import create_optimizer
from inference.consistency_sat import checkTautologies, test_weakly, consistency
from inference.weakly_system_z_rank import SystemZRankZ3

### some cleanup and some more documentation of class' funcitonalities pending

def filtersubsets(k, J):
    return [q for q in k if all([(t in J) for t in q])]

def filterdictJ(J, vmin):
    #print(J,vmin)
    jkeys = J
    interim = {i:k for i,k in vmin.items() if i in jkeys}
    result = {i:filtersubsets(k,jkeys) for i,k in interim.items()} ### can this map down a sublist to zero?
    return result

def naively_make_naivecinference(belief_base):
    epistemic_state = dict()
    epistemic_state['belief_base'] = belief_base
    epistemic_state['smt_solver'] = 'z3'
    epistemic_state['pmaxsat_solver'] = 'rc2'
    epistemic_state['result_dict'] = dict()
    epistemic_state['preprocessing_done'] = False
    epistemic_state['preprocessing_timed_out'] = False
    epistemic_state['preprocessing_time'] = 0
    epistemic_state['kill_time'] = 0
    return epistemic_state

class WeakCInference():
    def __init__(self, belief_base):
        self.epistemic_state = naively_make_naivecinference(belief_base)
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
        eta = {i: Symbol(f'eta_{i}', INT) for i, _ in self.epistemic_state['J_delta'].items()}
        gteZeros = [GE(e, Int(0)) for e in eta.values()]
        vSums = self.makeSummation(self.epistemic_state['vMin'])
        fSums = self.makeSummation(self.epistemic_state['fMin'])
        csp = self.encoding(eta, vSums, fSums)
        csp.extend(gteZeros)
        return csp


    def preprocess_belief_base(self) -> None:
        tseitin_transformation = TseitinTransformation(self.epistemic_state)
        tseitin_transformation.belief_base_to_cnf(True, True, True)

        ### check weakly consistency
        is_weakly = test_weakly(self.epistemic_state['belief_base'])
        assert(is_weakly)
        ### Compute tolerance partition
        self.epistemic_state['partition'],_ = consistency(self.epistemic_state['belief_base'], 'z3', True)

        ### compute J_delta
        J_inf = self.epistemic_state['partition'][-1]
        J_delta = dict()
        solver = Solver(name=self.epistemic_state['smt_solver'])
        [solver.add_assertion(Implies(c.antecedence,c.consequence)) for c in J_inf]
        for i,c in self.epistemic_state['belief_base'].conditionals.items():
            if solver.solve([c.make_A_then_not_B()]):
                J_delta[i] = c
        ### hold them in epistemic state? 
        self.epistemic_state['J_delta'] = J_delta
    
        ## TODO compiling base_csp happens more dynamically now, based on the query
        self.compile_constraint()
        self.base_csp = self.translate()


    def inference(self, query: Conditional) -> bool:
        sysz = SystemZRankZ3(self.epistemic_state['belief_base'])
        vf, ff = sysz.rank_query(query)
        infty = float('inf')
        if ff == infty: return True
        if vf == infty: return False

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
        J_delta = set(self.epistemic_state['J_delta'].keys())

        V = {i:v for i, v in self.epistemic_state['v_cnf_dict'].items() if i in J_delta}
        F = {i:f for i, f in self.epistemic_state['f_cnf_dict'].items() if i in J_delta}
        NF = {i:f for i, f in self.epistemic_state['nf_cnf_dict'].items()}

        self.epistemic_state['wv_cnf_dict'] = V
        self.epistemic_state['wf_cnf_dict'] = F
        self.epistemic_state['wnf_cnf_dict'] = NF

        for leading_conditional in [V,F]:
            for i, conditional in leading_conditional.items():
                xMins = []
                wcnf = WCNF()
                [wcnf.append(c) for c in conditional]
                [wcnf.append(s, weight=1) for j, softc in NF.items() if i != j for s in softc] ### amazing python construction fr fr 
                
                optimizer = create_optimizer(self.epistemic_state)
                xMins_lst = optimizer.minimal_correction_subsets(wcnf, ignore=[i])

                if leading_conditional is V:
                    self.epistemic_state['vMin'][i] = filtersubsets(xMins_lst,J_delta)
                else: 
                    self.epistemic_state['fMin'][i] = filtersubsets(xMins_lst,J_delta)

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
        #print(transformed_conditionals)

        J_delta = self.epistemic_state['J_delta'].keys()
        

        V = {i:v for i, v in self.epistemic_state['v_cnf_dict'].items() if i in J_delta}
        F = {i:f for i, f in self.epistemic_state['f_cnf_dict'].items() if i in J_delta}
        NF = {i:f for i, f in self.epistemic_state['wnf_cnf_dict'].items()}
        #print(NF)
        #print(transformed_conditionals)

        countv = 0
        countf = 0
        for conditional in transformed_conditionals:
            xMins = []
            wcnf = WCNF()
            [wcnf.append(c) for c in conditional]
            [wcnf.append(s, weight=1) for j, softc in NF.items() for s in softc]
            
            optimizer = create_optimizer(self.epistemic_state)
            xMins_lst = optimizer.minimal_correction_subsets(wcnf)
            
            if conditional is transformed_conditionals[0]:
                countv+=1
                vMin = filtersubsets(xMins_lst,J_delta)
            else: 
                countf+=1
                fMin = filtersubsets(xMins_lst, J_delta)

        vSum = self.makeSummation({0:vMin})
        fSum = self.makeSummation({0:fMin})
        mv, mf = self.freshVars(0)
        vM = self.minima_encoding(mv, vSum[0])
        fM = self.minima_encoding(mf, fSum[0])
        #print(countv, countf)
        #print(f"vM {vSum}")
        #print(f"fM {fSum}")
        csp = vM + fM + [GE(mv, mf)]
        #print(f"csp {csp}")
        return csp ,(time_ns()/(1e+6)-start_time)

