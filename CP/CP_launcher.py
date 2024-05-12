import pymzn
import os

def solve_mzn(mzn_file, dzn_file):
    from minizinc import Instance, Model, Solver

    # Load n-Queens model from file
    model = Model(mzn_file)

    model.add_file(dzn_file)
    # Find the MiniZinc solver configuration for Gecode
    gecode = Solver.lookup("gecode")
    # Create an Instance of the n-Queens model for Gecode
    instance = Instance(gecode, model)
    # Assign 4 to n
    # instance["n"] = 4
    result = instance.solve()
    # Output the array q
    return result

if __name__=='__main__':

    script_dir = os.path.dirname(os.path.abspath(__file__))

    os.chdir(script_dir)
    # Example usage
    mzn_file = 'toy_solver.mzn'
    dzn_file = '../instances_dzn/inst01.dzn'
    solution = solve_mzn(mzn_file, dzn_file)
    print(solution)
