from minizinc import Instance, Model, Solver
from datetime import timedelta
from utils import *
import math
import time


def solve_mzn(mzn_file, dzn_file, solver, params):
    model = Model(mzn_file)
    model.add_file(dzn_file)
    solver = Solver.lookup(solver)
    instance = Instance(solver, model)

    result = instance.solve(**params)

    return result


def launch(instances: list, model: str = 'model.mzn', solver: str = 'chuffed', params: dict = None, verbose=False):
    '''
    Parameters:
    instances (list): A list of file paths to the instance files to be solved.
    model (str): The file path to the MiniZinc model file.
    solver (str): The solver to use for solving the instances.
    params (dict): Additional parameters to pass to the solver.

    Returns:
    dict: A dictionary where keys are instance file paths and values are the solutions.
    '''
    if params == None:
        params = {
            'timeout': timedelta(seconds=300),
            'free_search': False
        }

    results = []
    for instance in instances:
        execTime = time.time()
        print(f"Solving {instance} ...")
        solution = solve_mzn('CP/'+model, instance, solver, params)
        execTime = math.floor(time.time()-execTime)
        if verbose:
            print(solution, getattr(solution, 'statistics'))
        if execTime > params['timeout'].total_seconds():
            execTime = math.floor(params['timeout'].total_seconds())
        try:
            obj = solution['objective']
        except:
            obj = -1
            # print(solution,type(solution),str(solution))
        if obj == -1:
            obj = 'N/A'
        if str(solution) != 'None':
            solution = tolist(solution['stops'])
        else:
            solution=[]
        results.append({
            "time": execTime,
            "optimal": (execTime < params['timeout'].total_seconds()),
            "obj": obj,
            "sol": solution
        })
        # print(solution)

    return results

def solve_instance(
        instance_file,
        model,
        solver,
        params,
        verbose=False
):
    execTime = time.time()
    solution = solve_mzn('CP/'+model, instance_file, solver, params)
    execTime = math.floor(time.time()-execTime)
    if verbose:
        print(solution, getattr(solution, 'statistics'))
    if execTime > params['timeout'].total_seconds():
        execTime = math.floor(params['timeout'].total_seconds())
    try:
        obj = solution['objective']
    except:
        obj = -1
    if obj == -1:
        obj = 'N/A'
    if str(solution) != 'None':
        solution = tolist(solution['stops'])
    else:
        solution=[]
    return {
        "time": execTime,
        "optimal": (execTime < params['timeout'].total_seconds()),
        "obj": obj,
        "sol": solution
    }


# if __name__ == '__main__':
#     # used for testing purposes
#     # this_dir = os.path.dirname(os.path.abspath(__file__))
#     # os.chdir(this_dir)

#     instances_folder = '../instances_dzn'
#     # instances_folder='.'
#     instances = [instances_folder+'/'+instance for instance in os.listdir(
#         instances_folder) if instance.endswith('.dzn')]
#     instances.sort()
#     mzn_file = 'model.mzn'
#     mzn_file = 'model_drunky.mzn'
#     # mzn_file = 'working_solver.mzn'

#     print(launch(instances[:1]))
