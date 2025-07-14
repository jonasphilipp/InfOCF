from pysmt.shortcuts import Solver, Symbol
from pysmt.typing import INT

from inference.c_inference import CInference
from inference.inference_operator import create_epistemic_state
from parser.Wrappers import parse_belief_base

# Create a small birds belief base for more targeted testing
str_birds = (
    "signature\nb,p,f,w\n\nconditionals\nbirds{\n(f|b),\n(!f|p),\n(b|p),\n(w|b)\n}"
)
bb_birds = parse_belief_base(str_birds)

# Configure solvers
smt_solver = "z3"
pmaxsat_solver = "rc2"


epistemic_state_z_birds = create_epistemic_state(
    bb_birds,
    inference_system="system-z",
    smt_solver=smt_solver,
    pmaxsat_solver=pmaxsat_solver,
    weakly=False,
)

cinference = CInference(epistemic_state_z_birds)

cinference.preprocess_belief_base(0)
solver = Solver(name=smt_solver)
base_csp = cinference.base_csp
for constraint in base_csp:
    solver.add_assertion(constraint)
is_sat = solver.solve()
print(f"Constraints are satisfiable: {is_sat}")

if is_sat:
    # Get the model only if satisfiable
    model = solver.get_model()
    print("Vector:")
    for i in epistemic_state_z_birds["belief_base"].conditionals.keys():
        print(f"eta_{i}: {model[Symbol(f'eta_{i}', INT)]}")
else:
    print("No satisfying model exists for the given constraints")
