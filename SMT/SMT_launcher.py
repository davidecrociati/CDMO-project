import os
import time
import math
from SMT.SMT_utils import *
import SMT.SMT_solver as solver
from datetime import timedelta

def launch(models: list, params: dict = None, verbose=False):

    if params == None:
        params = {
            'timeout': 300_000, # microseconds
        }  # those are default

    results = []
    for model in models:
        print(f'Solving {model}...')
        execTime = time.time()
        solution = solver.solve(model,params)
        execTime = math.floor(time.time()-execTime)
        if execTime > params['timeout']/1000:
            execTime = params['timeout']/1000
        obj = solution[0]
        if obj == -1:
            obj = 'n/a'
        results.append({
            "time": execTime,
            "optimal": (execTime < params['timeout']/1000),
            "obj": obj,
            "sol": solution[1]
        })

    return results

    
def generate_smt2_models(instances,models_path):
    if not os.path.exists(models_path):
        os.makedirs(models_path)

    file_paths = []

    for instance in instances:
        model_content=generate_smt2_model(instance)
        filename=models_path+'/model_'+os.path.splitext(os.path.basename(instance))[0]+'.smt2'
        with open(filename,'w') as file:
            file.write(model_content)
        file_paths.append(filename)
    
    return file_paths

if __name__ == "__main__":
    launch('instances_dzn/inst01.dzn')
