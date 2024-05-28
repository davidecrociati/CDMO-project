from datetime import timedelta
from  utils.utils import parse_dzn
import SAT.SAT_solver as SAT_solver
from SAT.SAT_utils import *
import time
import math


def solve_instance(
        instance_file,
        params,
        search_strategy="lower_upper",              # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        model="1-hot",                              # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        verbose=False
):
    instance_data=parse_dzn(instance_file)
    # obj='N/A' # inserito dentro solve_strategy
    try:
        if type(params['timeout'])==timedelta:
            params['timeout']=params['timeout'].total_seconds()
    except: pass
    # aux=params.copy() # inserito dentro solve_strategy
    execTime = time.time()
    
    obj, solution = solve_strategy(instance_data, model, search_strategy, params, execTime, verbose=True, binary_cut=8)
                    
    execTime = math.floor(time.time()-execTime)
    if verbose:
        print(solution)
    # solution=parse_solution(solution)
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

# TODO : TEORICAMENTE INUTILE --> buttiamo via ?
# def launch(instances: list, params: dict = None, verbose=False):

#     if params == None:
#         params = {
#             'timeout': timedelta(seconds=300).total_seconds()
#         }  # those are default

#     results = []
#     for instance in instances:
#         print(f'Solving {instance}...')
#         execTime = time.time()
#         instance_data = parse_dzn(instance)
#         try:
#             if type(params['timeout'])==timedelta:
#                 params['timeout']=params['timeout'].total_seconds() # milliseconds
#         except: pass
#         aux=params.copy()
#         for max_path in range(instance_data['lower_bound'],instance_data['upper_bound']+1):
#             aux['timeout'] -= (time.time()-execTime)
#             if aux['timeout'] <= 0 : break
#             res, (obj, solution) = SAT_solver.solve_pelle(instance_data, max_path, aux)
#             if res == "sat" : break
#         execTime = math.floor(time.time()-execTime)
#         if execTime > params['timeout']:
#             execTime = params['timeout']
#         if obj == -1:
#             obj = 'N/A'
#         results.append({
#             "time": execTime,
#             "optimal": (execTime < params['timeout']),
#             "obj": obj,
#             "sol": solution
#         })

#     return results


# if __name__=='__main__':
#     this_dir = os.path.dirname(os.path.abspath(__file__))
#     os.chdir(this_dir)

#     file='instances_dzn/inst01.dzn'
#     file2='instances_dzn/inst02.dzn'

#     # print(parse_dzn(file))
#     print(launch([file,file2]))
