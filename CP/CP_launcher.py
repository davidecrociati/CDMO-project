from minizinc import Instance, Model, Solver
from datetime import timedelta
import os
import math
from utils import *
import time

def solve_mzn(mzn_file, dzn_file,solver,params):
    model = Model(mzn_file)
    model.add_file(dzn_file)
    solver = Solver.lookup(solver)
    instance = Instance(solver, model)
    # TODO fargli passare i parametri (quali ?)

    result = instance.solve(**params,free_search=True)

    return result

def launch(instances:list, model:str='model.mzn', solver:str='chuffed', params:dict=None,verbose=False):
    '''
    Parameters:
    instances (list): A list of file paths to the instance files to be solved.
    model (str): The file path to the MiniZinc model file.
    solver (str): The solver to use for solving the instances.
    params (dict): Additional parameters to pass to the solver.

    Returns:
    dict: A dictionary where keys are instance file paths and values are the solutions.
    '''
    this_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(this_dir)

    if params==None:
        params={'timeout':timedelta(seconds=300)}

    results=[]
    for instance in instances[:]:
        print(f"Solving {instance} ...")
        execTime=time.time()
        solution = solve_mzn(model, '../'+instance,solver,params)
        execTime=math.floor(time.time()-execTime)
        if verbose:print(solution,getattr(solution,'statistics'))
        if execTime>params['timeout'].total_seconds():
            execTime=params['timeout'].total_seconds()
        try:
            obj=solution['objective']
        except KeyError:
            obj=-1
            # print(solution,type(solution),str(solution))
        if obj==-1:
            obj='n/a'
        if str(solution)!='None':
            solution=tolist(solution['stops'])
        results.append({
            "time" : execTime,
            "optimal" : (execTime<params['timeout'].total_seconds()),
            "obj" : obj,
            "sol" : solution
        })
        
    return results

if __name__=='__main__':
    # used for testing purposes
    this_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(this_dir)

    instances_folder='../instances_dzn'
    # instances_folder='.'
    instances=[instances_folder+'/'+instance for instance in os.listdir(instances_folder) if instance.endswith('.dzn')]
    instances.sort()
    mzn_file = 'model.mzn'
    mzn_file = 'model_drunky.mzn'
    # mzn_file = 'working_solver.mzn'
    
    print(launch(instances[:1]))