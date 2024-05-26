import os
import time
import math
from SMT.SMT_utils import *
from SMT.SMT_solver import *
from datetime import timedelta

# def launch(models: list, params: dict = None, verbose=False):

#     if params == None:
#         params = {
#             'timeout': 300_000, # microseconds
#         }  # those are default

#     results = []
#     for model in models:
#         print(f'Solving {model}...')
#         execTime = time.time()
#         # solution = solve(model,params)
#         execTime = math.floor(time.time()-execTime)
#         if execTime > params['timeout']/1000:
#             execTime = params['timeout']/1000
#         obj = solution[0]
#         if obj == -1:
#             obj = 'N/A'
#         results.append({
#             "time": execTime,
#             "optimal": (execTime < params['timeout']/1000),
#             "obj": obj,
#             "sol": solution[1]
#         })

#     return results

def solve_instance(
        instance_file,
        solver,
        params,
        verbose=False
):
    solve=None
    match solver:
        case 'z3':
            solve=solve_z3
        case 'cvc4':
            solve=solve_cvc4
        case _:
            raise KeyError('Unsupported solver')
    instance_data=parse_dzn(instance_file)
    model_head,model_tail=generate_smt2_model(instance_data)
    obj='N/A'
    model=''
    try:
        if type(params['timeout'])==timedelta:
            params['timeout']=params['timeout'].total_seconds()
    except: pass
    aux=params.copy()
    execTime = time.time()
    solution=[]
    best_model=None
    max_path=instance_data['upper_bound']
    while max_path>=instance_data['lower_bound']:
        model=add_objective(instance_data['num_couriers'],max_path,model_head,model_tail)
        try:
            aux['timeout']-=(time.time()-execTime)
            if aux['timeout']<=0:
                break
        except:pass
        # print('avalaible time:',aux['timeout'])
        result,sol,distances=solve(model,aux)
        if result=='unsat':
            break
        obj=max(distances)
        max_path=obj-1
        solution=parse_solution(sol)
        best_model=model
    execTime = math.floor(time.time()-execTime)
    if verbose:
        print(solution)
    if not solution:
        execTime=math.floor(params['timeout'])
    try:
        if execTime > params['timeout']:
            execTime = math.floor(params['timeout'])
        return {
            "time": execTime,
            "optimal": (execTime < params['timeout']),
            "obj": obj,
            "sol": solution
        },best_model
    except:
        return {
            "time": execTime,
            "optimal": True,
            "obj": obj,
            "sol": solution
        },best_model
    # TRY-EXCEPT are for when there is no timeout key in the dict

    
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