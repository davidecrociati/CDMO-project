from MIP.MIP_solver import *
from utils  import *
from datetime import timedelta
import math
import time

def solve_instance(
        instance_file,
        solver,
        params,
        model_params:dict =None,
        verbose =False,
):
    instance_data =parse_dzn(instance_file)
    obj ='N/A'
    model =''
    try:
        if type(params['timeout']) == timedelta:
            params['timeout'] = params['timeout'].total_seconds()
    except: pass    
    
    aux = params.copy()
    
    execTime = time.time()
    solution = []
    best_model = None
    opt = False

    solution, obj = solve(solver, params, instance_data)
    # print('total effective time:',time.time()-execTime)
    execTime = math.floor(time.time()-execTime)
    
    if not solution:
        execTime = math.floor(params['timeout'])
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
    pass

