from minizinc import Instance, Model, Solver
from datetime import timedelta
import os
import subprocess
import math
from utils.utils import *

def solve_mzn(mzn_file, dzn_file,solver,params):
    command = ['minizinc',
               '-f',
               '-v',
               '--time-limit', f'{params["timeout"]}',
               '--solver', f'{solver}',
               f'{mzn_file}', f'{dzn_file}']
    result = subprocess.run(command, text=True, capture_output=True)#, shell=True, check=True, text=True, capture_output=True)
    print(result.stderr)

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
    # print(instances)
    for instance in instances[:]:
        if verbose:print(f"Solving {instance} ...")
        
        solution = solve_mzn(model, '../'+instance,solver,params)
        stats = getattr(solution,'statistics')
        try:
            execTime = math.floor(stats['time'].total_seconds())
            obj=stats['objective']
        except KeyError:
            print(solution)
            # execTime=params['timeout'].total_seconds()
        if obj==-1:
            obj='n/a'
        results.append({
            "time" : execTime,
            "optimal" : (execTime<params['timeout'].total_seconds()),
            "obj" : obj,
            "sol" : tolist(solution)
            # output del modello (da fare su una riga sola)
            # ^ DIPENDE DA COME LEGGE I FILE IL CHECKER
            # ^ SE CI STA UN QUALCOSA CHE LEGGE I JSON BENE 
            # ^ NON PENSO SIA NECESSARIO
        })
        
        if verbose:print(stats)
        
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