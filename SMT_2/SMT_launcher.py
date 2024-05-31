import os
import time
import math
# from SMT.SMT_utils import *
from SMT_2.SMT_solver import *
from datetime import timedelta


def solve_instance(
        instance_file,
        solver,
        params,
        model_params:dict=None,
        verbose=False,
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
    model_params=check_model_params(model_params)
    # print(model_params)
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
    opt=False

    solution,obj = solve(params, instance_data)

    execTime = math.floor(time.time()-execTime)
    
    if not solution:
        execTime=math.floor(params['timeout'])
        opt = False
    try:
        if execTime >= params['timeout']:
            execTime = math.floor(params['timeout'])
            opt = False
        else:
            opt = True
        return {
            "time": execTime,
            "optimal": opt,
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
    # TRY-EXCEPT are for when there is no timeout key in the dictionary