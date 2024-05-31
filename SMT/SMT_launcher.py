import os
import time
import math
# from SMT.SMT_utils import *
from SMT.SMT_solver import *
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
    model_head,model_tail=generate_model(instance_data,**model_params)
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
    opt=False
    num_couriers=instance_data['num_couriers']
    use_arrays=model_params['use_arrays']
    use_successors=model_params['use_successors']
    impose_lower_bound=model_params['impose_lower_bound']
    while max_path>=instance_data['lower_bound']:
        model=add_objective(
            instance_data['num_couriers'],
            max_path,
            model_head,
            model_tail,
            arrays=use_arrays,
            impose_lower_bound=impose_lower_bound)
        try:
            aux['timeout']=params['timeout']-(time.time()-execTime)
            if aux['timeout']<=0:
                if verbose:print('timeout! passati ',math.floor(time.time()-execTime))
                break
            if verbose:print('available time:',aux['timeout'])
        except:
            print('error')
            pass
        result,sol,distances=solve(model,aux,use_arrays,use_successors,num_couriers)
        if result=='unsat':
            try:
                if params['timeout']-(time.time()-execTime)>0:
                    opt=True
                    if verbose:print(f'unsat con {max_path}. passati {time.time()-execTime}')
                else:    
                    if verbose:print('timeout! passati ',math.floor(time.time()-execTime))
            except: opt=True
            break
        obj=max(distances)
        max_path=obj-1  
        solution=parse_solution(sol,use_arrays)
        if verbose:print(f'found {obj}, {solution}')
        best_model=model
        if max_path<instance_data['lower_bound']:
            if verbose:print(f'arrivato al lower bound {max_path}, [{instance_data["lower_bound"]},{instance_data["upper_bound"]}]')
            opt=True
    execTime = math.floor(time.time()-execTime)
    if not solution:
        execTime=math.floor(params['timeout'])
    try:
        if execTime > params['timeout']:
            execTime = math.floor(params['timeout'])
        return {
            "time": execTime,
            "optimal": opt,
            "obj": obj,
            "sol": solution
        },best_model
    except:
        return {
            "time": execTime,
            "optimal": opt,
            "obj": obj,
            "sol": solution
        },best_model
    # TRY-EXCEPT are for when there is no timeout key in the dict

def generate_model(
        data,
        simmetry_method:str='>',
        use_successors=True,
        use_arrays=True,
        impose_lower_bound=False,
        redundancy=False
):
    # return generate_array_smt2_model(data)
    num_couriers = data['num_couriers']
    num_items = data['num_items']
    lower_bound = data['lower_bound']
    upper_bound = data['upper_bound']

    # ===== INSTANCE VARIABLES =====
    constants = f'''
(set-logic ALL)
(declare-fun num_couriers () Int)
(assert (= num_couriers {num_couriers}))
(declare-fun num_items () Int)
(assert (= num_items {num_items}))
(declare-fun lower_bound () Int)
(assert (= lower_bound {lower_bound}))
(declare-fun upper_bound () Int)
(assert (= upper_bound {upper_bound}))
'''.lstrip()
    
    variables=define_decision_variables(data,use_arrays)

    bin_packing=define_bin_packing(num_couriers,num_items,use_arrays)

    # start_end_depot=define_start_end(num_couriers,num_items,use_arrays)

    all_couriers_deliver=define_couriers_duty(num_couriers,num_items,use_arrays)

    # couriers_first_stops=define_first_stop_item(num_couriers,num_items,use_arrays)

    simmetry=define_simmetry(num_couriers,simmetry_method,use_arrays)

    all_items_delivered=define_deliver_everything(num_couriers,num_items,use_arrays) if redundancy else ''

    channeling=define_padding(num_couriers,num_items,use_arrays)

    item_carrier=define_courier_items(num_couriers,num_items,use_arrays)

    if use_successors:
        def_successors,distances_calculation=define_successors_distances(num_couriers,num_items,impose_lower_bound,use_arrays)
    else:
        distances_calculation=define_distances(num_couriers,num_items,use_arrays)

    model_head=f'''
{constants}
{variables}
{bin_packing}
{all_couriers_deliver}
{simmetry}
{all_items_delivered}
{channeling}
{item_carrier}
{def_successors if use_successors else ''}
{distances_calculation}
'''
    model_tail='(check-sat)\n(get-model)\n'

    return model_head,model_tail