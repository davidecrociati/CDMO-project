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
    if type(params['timeout'])==timedelta:
        params['timeout']=params['timeout'].total_seconds()
    execTime = time.time()
    aux=params.copy()
    for max_path in range(instance_data['lower_bound'],instance_data['upper_bound']+1):
        model=add_objective(instance_data['num_couriers'],1000,model_head,model_tail)
        aux['timeout']-=(time.time()-execTime)
        if aux['timeout']<=0:
            break
        # print('avalaible time:',aux['timeout'])
        result,solution=solve(model,aux)
        if result=='sat':
            obj=max_path
            break
    execTime = math.floor(time.time()-execTime)
    if verbose:
        print(solution)
    solution=parse_solution(solution)
    if not solution:
        model=None
        execTime=math.floor(params['timeout'])
    if execTime > params['timeout']:
        execTime = math.floor(params['timeout'])
    return {
        "time": execTime,
        "optimal": (execTime < params['timeout']),
        "obj": obj,
        "sol": solution
    },model

    
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
