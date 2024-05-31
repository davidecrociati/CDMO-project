from datetime import timedelta
from  utils.utils import parse_dzn
import SAT.SAT_solver as SAT_solver
from SAT.SAT_utils import *
import time
import math


def solve_instance(
        instance_file,
        params,
        
        search_strategy="lower_upper",                              # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        # search_strategy="upper_lower",                            # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        # search_strategy="binary_search",                          # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        # search_strategy="incremental_lower_upper",                # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        
        # model="1-hot",                                            # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        # model="binary",                                             # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        model="circuit",                                            # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        
        verbose_search=False, 
        verbose_solver=True,
        symmetry=True
):
    instance_data=parse_dzn(instance_file)
    
    try:
        if type(params['timeout'])==timedelta:
            params['timeout']=params['timeout'].total_seconds()
    except: pass
    
    execTime = time.time()
    obj, solution = solve_strategy(instance_data, model, search_strategy, params, execTime, 
                                    binary_cut=15,          # Non credo le selezioneremo mai dal main
                                    incremental_factor=30,  # Non credo le selezioneremo mai dal main
                                    symmetry=symmetry, verbose_search=verbose_search, verbose_solver=verbose_solver
                                )
                    
    execTime = math.floor(time.time()-execTime)
    
    if not solution:
        execTime=math.floor(params['timeout'])
        solution=[]
    try:
        if execTime > params['timeout']:
            execTime = math.floor(params['timeout'])
        return {
            "time": execTime,
            "optimal": (execTime < params['timeout']),
            "obj": obj,
            "sol": solution
        }
    except:
        return {
            "time": execTime,
            "optimal": True,
            "obj": obj,
            "sol": solution
        }