from minizinc import Instance, Model, Solver
from datetime import timedelta
import os

def solve_mzn(mzn_file, dzn_file):

    # Load n-Queens model from file
    model = Model(mzn_file)

    model.add_file(dzn_file)
    # Find the MiniZinc solver configuration for Gecode
    gecode = Solver.lookup("chuffed")
    # Create an Instance of the n-Queens model for Gecode
    instance = Instance(gecode, model)
    # Assign 4 to n
    result = instance.solve(timeout=timedelta(seconds=15))
    # Output the array q
    return result

if __name__=='__main__':
    script_dir = os.path.dirname(os.path.abspath(__file__))

    os.chdir(script_dir)
    # Example usage
    mzn_file = 'solver.mzn'
    dzn_file = '../instances_dzn/inst01.dzn'
    dzn_file = 'test/inst_test.dzn'
    solution = solve_mzn(mzn_file, dzn_file)
    print(solution)
