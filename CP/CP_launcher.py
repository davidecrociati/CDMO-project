import pymzn
import os

def solve_mzn(mzn_file, dzn_file):
    # Load the MiniZinc model
    model = pymzn.minizinc(mzn_file)

    # Load the MiniZinc data file
    data = pymzn.dzn_load(dzn_file)

    # Solve the MiniZinc model with the provided data
    result = pymzn.minizinc(model, data=data, output_mode='json')

    return result

if __name__=='__main__':

    script_dir = os.path.dirname(os.path.abspath(__file__))

    os.chdir(script_dir)
    # Example usage
    mzn_file = 'toy_solver.mzn'
    dzn_file = '../instances_dzn/inst01.dzn'
    solution = solve_mzn(mzn_file, dzn_file)
    print(solution)
