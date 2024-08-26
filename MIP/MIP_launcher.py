from MIP.MIP_solver import *
from utils  import *
from datetime import timedelta
import math

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
    
    solution = []
    best_model = None
    opt = False

    solution, obj, opt, execTime = solve(solver, params, instance_data)
    try:
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

