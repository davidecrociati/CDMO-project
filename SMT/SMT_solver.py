from SMT.SMT_utils import *
from z3 import *

def solve(model,params:dict):
    solver = Solver()
    solver.set(unsat_core=True)
    solver.set(**params)
    solver.add(parse_smt2_file(model))
    
    result = solver.check()
    
    if result == sat:
        get_variables(solver.model())
    else:
        print("UNSAT")

    return parse_solution(result)