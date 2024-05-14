from minizinc import Instance, Model, Solver
from datetime import timedelta
import os
import time

def current_milli_time():
    return round(time.time() * 1000)

def solve_mzn(mzn_file, dzn_file, solver="gecode", stop_time=300):

    # Load n-Queens model from file
    model = Model(mzn_file)
    model.add_file(dzn_file)
    
    # Find the MiniZinc solver configuration for Gecode
    gecode = Solver.lookup(solver)
    
    # Create an Instance of the n-Queens model for Gecode
    instance = Instance(gecode, model)
    
    start_time = current_milli_time()
    
    # Assign 4 to n
    output = str(instance.solve(timeout=timedelta(seconds=15)))
    
    # We pick only the first 2 rows
    obj = output.split("\n")[0]
    solution = output.split("\n")[1]
    
    # Compute execution time
    exec_time = current_milli_time() - start_time
    
    # Decide if optimal or not
    optimal = str((exec_time < stop_time*1000))

    # Output the array q
    # return output
    
    # Real output
    return {solver:{
        "time" : int(exec_time/1000), 
        "optimal" : optimal,
        "obj" : obj,
        "sol" : solution
    }}

if __name__=='__main__':
    script_dir = os.path.dirname(os.path.abspath(__file__))

    os.chdir(script_dir)
    # Example usage
    mzn_file = 'solver.mzn'
    dzn_file = '../../instances_dzn/inst01.dzn'
    solution = solve_mzn(mzn_file, dzn_file)
    print(solution)
