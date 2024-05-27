from datetime import timedelta
from  utils.utils import parse_dzn
import SAT.SAT_solver as SAT_solver
import time
import math


def solve_instance(
        instance_file,
        params,
        mode="incremental_lower_upper", # TODO: da far selezionare nel main più avanti, per ora si chiama da qui
        verbose=False
):
    instance_data=parse_dzn(instance_file)
    obj='N/A'
    try:
        if type(params['timeout'])==timedelta:
            params['timeout']=params['timeout'].total_seconds()
    except: pass
    aux=params.copy()
    execTime = time.time()
    
    # TODO: inserire la logica in una funzione perchè illegibile qui
    match mode:
        case "lower_upper" :
            # Mode 1: lower --> upper
            for max_path in range(instance_data['lower_bound'],instance_data['upper_bound']+1):
                try:
                    aux['timeout'] = params['timeout']-(time.time()-execTime)
                    if aux['timeout']<=0:
                        break
                except:pass
                # print('avalaible time:',aux['timeout'])
                # t = time.time()
                result, solution = SAT_solver.solve(instance_data, max_path, aux)
                # print(f"Esecuzione avvenuta in {time.time()-t} secondi")
                if result=='sat':
                    obj=max_path
                    break
                
        case "upper_lower" :
            # Mode 2: upper --> lower 
            for max_path in range(instance_data['upper_bound'],instance_data['lower_bound']-1, -1):
                # print(f"max_path={max_path}")
                try:
                    aux['timeout'] = params['timeout']-(time.time()-execTime)
                    # print(f"Mancano {aux['timeout']} secondi")
                    if aux['timeout']<=0:
                        break
                except:pass
                # print('avalaible time:',aux['timeout'])
                # t = time.time()
                result, sol = SAT_solver.solve(instance_data, max_path, aux)
                # print(f"Sono passati {time.time()-t} secondi")
                # print(result)
                if result=='sat' : 
                    obj=max_path
                    solution = sol
            
        case "binary_search" :
            # Mode 3: binary search
            lower_bound = instance_data['lower_bound']
            upper_bound = instance_data['upper_bound']
            solution = []
            while lower_bound <= upper_bound:
                mid = (lower_bound + upper_bound) // 2
                try:
                    aux['timeout'] = params['timeout']-(time.time()-execTime)
                    if aux['timeout'] <= 0:
                        break
                except:
                    pass

                # t = time.time()
                result, sol = SAT_solver.solve(instance_data, mid, aux)
                # print(f"Sono passati {time.time()-t} secondi")

                if result == 'sat':
                    obj = mid
                    solution = sol
                    # print(solution)
                    upper_bound = mid - 1  # Try for a smaller feasible solution
                else:
                    lower_bound = mid + 1  # Try for a larger feasible solution
        
        case "incremental_lower_upper":
            # Mode 4: incremental lower --> upper
            lower_bound = instance_data['lower_bound']
            upper_bound = instance_data['upper_bound']
            incremental_factor = 2 # magic number to choose
            solution = []
            bound = lower_bound

            while bound <= upper_bound:
                try:
                    aux['timeout'] = params['timeout'] - (time.time() - execTime)
                    if aux['timeout'] <= 0:
                        break
                except:
                    pass

                result, sol = SAT_solver.solve(instance_data, bound, aux)
                print(f"{bound}) In the incremental part i found: ", sol)

                if result == 'sat':
                    # We have found a sat solution but maybe it's not the smallest
                    obj = bound
                    solution = sol
                    bound -= 1 # we make a step back to check
                    while bound >= lower_bound:
                        try:
                            aux['timeout'] = params['timeout'] - (time.time() - execTime)
                            if aux['timeout'] <= 0:
                                break
                        except:
                            pass

                        result, sol = SAT_solver.solve(instance_data, bound, aux)
                        print(f"{bound}) In the backtracking part i found: ", sol)
                        
                        if result == 'sat':
                            # The previous solution wasn't the smalles, continue the search
                            obj = bound
                            solution = sol
                        else:
                            # The previous one was the smalles
                            break
                        bound -= 1
                    break  # We found the smallest or the timout ended
                else:
                    # The solution is unsat so we need a bigger bound
                    next_bound = bound * incremental_factor
                    # Check not to use a too big bound
                    if next_bound > upper_bound : bound += 1 
                    else : bound = next_bound
                    print(f"Unsar, try bound = {bound}")
                    
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
