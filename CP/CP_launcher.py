from minizinc import Instance, Model, Solver
from datetime import timedelta
import os

def solve_mzn(mzn_file, dzn_file):
    # Load n-Queens model from file
    model = Model(mzn_file)

    model.add_file(dzn_file)
    # Find the MiniZinc solver configuration for Gecode
    solver = Solver.lookup("chuffed")
    # Create an Instance of the n-Queens model for Gecode
    instance = Instance(solver, model)
    # Assign 4 to n
    result = instance.solve(timeout=timedelta(seconds=300))
    # Output the array q
    return result

if __name__=='__main__':
    script_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(script_dir)

    instances_folder='../instances_dzn'
    instances=[instances_folder+'/'+instance for instance in os.listdir(instances_folder) if instance.endswith('.dzn')]
    mzn_file = 'solver.mzn'

    for instance in instances[15:16]:
        solution = solve_mzn(mzn_file, instance)
        print(solution)
        # TODO il json