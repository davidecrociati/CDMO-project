import sys,os
sys.path.append(os.path.dirname(os.path.dirname(__file__)))
from utils import parse_dzn
import z3

def generate_smt2_model(dzn_instance,obj=226):# TODO remove the 14
    instance_data=parse_dzn(dzn_instance)

    num_couriers = instance_data['num_couriers']
    num_items = instance_data['num_items']
    courier_capacities = instance_data['courier_capacities']
    item_sizes = instance_data['item_sizes']
    distances = instance_data['distances']
    lower_bound = instance_data['lower_bound']
    upper_bound = instance_data['upper_bound']

    # ===== INSTANCE VARIABLES =====
    model = f'''
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
    for i, size in enumerate(courier_capacities, start=1):
        model += f'(declare-fun courier_{i}_capacity () Int)\n'
        model += f'(assert (= courier_{i}_capacity {size}))\n'
    for i, size in enumerate(item_sizes, start=1):
        model += f'(declare-fun item_{i}_size () Int)\n'
        model += f'(assert (= item_{i}_size {size}))\n'
    for i in range(num_items+1):
        for j in range(num_items+1):
            model += f'(declare-fun distance_{i+1}_{j+1} () Int)\n'
            model += f'(assert (= distance_{i+1}_{j+1} {distances[i][j]}))\n'

    # ===== DECISION VARIABLES =====
    for c in range(1,num_couriers+1):
        for i in range(3,num_items+2):
            model += f'(declare-fun stop_{c}_{i} () Int)\n'
            model += f'(assert (>= stop_{c}_{i} 1))\n'
            model += f'(assert (<= stop_{c}_{i} {num_items+1}))\n'
    for i in range(1,num_items+1):
        model += f'(declare-fun item_{i}_resp () Int)\n'
        model += f'(assert (>= item_{i}_resp 1))\n'
        model += f'(assert (<= item_{i}_resp {num_couriers}))\n'
    for c in range(1,num_couriers+1):
        model += f'(declare-fun distance_{c}_traveled () Int)\n'
        model += f'(assert (>= distance_{c}_traveled 0))\n'
        model += f'(assert (<= distance_{c}_traveled {upper_bound}))\n'
    
    model += f'''
(declare-fun longest_trip () Int)
(assert (>= longest_trip {lower_bound}))
(assert (<= longest_trip {upper_bound}))
'''.lstrip()
    # TODO decomenntare se serve successors
    # for i in range(1,num_items+1):
    #     model += f'(declare-fun successors_{i} () Int)\n'
    #     model += f'(assert (>= successors_{i} 0))\n'
    #     model += f'(assert (<= successors_{i} {num_items+1}))\n'

    # ===== CONSTRAINTS =====
    # bin packing
    # -- loads does not exceed capacities
    for c in range(1,num_couriers+1):
        model+=f'(assert (>= courier_{c}_capacity (+'
        for i in range(1,num_items+1):
            model+=f'(ite (= item_{i}_resp {c}) item_{i}_size 0)'
        model+=')))\n'

    # start and end in depot
    for c in range(1,num_couriers+1):
        model += f'(declare-fun stop_{c}_1 () Int)\n'
        model += f'(declare-fun stop_{c}_{num_items+2} () Int)\n'
        model += f'(assert (= stop_{c}_1 {num_items+1}))\n'
        model += f'(assert (= stop_{c}_{num_items+2} {num_items+1}))\n'

    # each courier appears on item resp
    for c in range(1,num_couriers+1):
        model+=f'(assert (or '
        for i in range(1,num_items+1):
            model+=f'(= item_{i}_resp {c})'
        model+='))\n'

    # each couriers must deliver something on 1st stop
    for c in range(1,num_couriers+1):
        model += f'(declare-fun stop_{c}_2 () Int)\n'
        model += f'(assert (>= stop_{c}_2 1))\n'
        model += f'(assert (<= stop_{c}_2 {num_items}))\n'

    # all items must be delivered
    # for i in range(1,num_items+1):
    #     model+=f'(assert (or '
            # TODO in teoria è ridondante, vediamo se servirà metterlo

    # channeling; stops after completing the delivers must be depot
    for c in range(1,num_couriers+1):
        for i in range(1,num_items+1):
            # lhs=>rhs
            # rhs=>lhs
            lhs=f'(<= {i} (+ '
            for i_ in range(1,num_items+1):
                lhs+=f'(ite (= item_{i_}_resp {c}) 1 0) '
            lhs+=f'))'
            rhs=f'(< stop_{c}_{i+1} {num_items+1})'
            model+=f'(assert (=> {lhs} {rhs}))\n'
            model+=f'(assert (=> {rhs} {lhs}))\n'

    # items delivered by c must appear in its row
    for c in range(1,num_couriers+1):
        for i in range(1,num_items+1):
            model+=f'(assert (=> (= item_{i}_resp {c}) (or '
            for i_ in range(1,num_items+1):
                model+=f'(= stop_{c}_{i_+1} {i})'
            model+=f')))\n'

    # create successors
    # TODO maybe

    # compute distances with successor
    # TODO maybe

    # compute distances
    for c in range(1,num_couriers+1):
        model+=f'(assert (= distance_{c}_traveled (+ '
        for i in range(1,num_items+2):
            for j in range(1,num_items+2):
                for k in range(1,num_items+2):
                    model+=f'(ite (and (= stop_{c}_{i} {j})(= stop_{c}_{i+1} {k})) distance_{j}_{k} 0)'
        model+=f')))\n'
    # TODO continue...

    # objective
    # come fare il max????
    for c in range(1,num_couriers+1):
        model+=f'(assert (<= distance_{c}_traveled {obj}))\n'
        
    model+='(check-sat)\n(get-model)'

    return model


def parse_solution(result):
    # TODO

    return -1,[]

def get_variables(model,print_names=False):
    get_responsabilities(model,print_names)
    get_stops(model,print_names)
    get_distances(model,print_names)

def get_responsabilities(model,print_names):
    variables = []
    for var in model:
        if '_resp' in var.name():
            variables.append((var, model[var]))
    sorted_variables = sorted(variables, key=lambda x: x[0].name())
    print('resp:',[v[1] for v in sorted_variables],[v[0] for v in sorted_variables] if print_names else '')

def get_stops(model,print_names):
    # variables = []
    # for var in model:
    #     if 'stop_' in var.name():
    #         variables.append((var, model[var]))
    # sorted_variables = [(str(name),val) for name,val in sorted(variables, key=lambda x: x[0].name())]
    matrix=[]
    matrix_names=[]
    num_c=int(str(model[[var for var in model if 'num_couriers' in var.name()][0]]))
    num_i=int(str(model[[var for var in model if 'num_items' in var.name()][0]]))
    for i in range(1,num_c+1):
        matrix.append([])
        matrix_names.append([])
        for j in range(1,num_i+3):
            node=[var for var in model if f'stop_{i}_{j}' in var.name()][0]
            matrix[i-1].append(model[node])
            matrix_names[i-1].append(node)

    print('stops:')
    for i in range(len(matrix)):
        print('  ',matrix[i],matrix_names[i] if print_names else '')

def get_distances(model,print_names):
    variables = []
    for var in model:
        if '_traveled' in var.name():
            variables.append((var, model[var]))
    sorted_variables = sorted(variables, key=lambda x: x[0].name())
    print('dists:',[v[1] for v in sorted_variables],[v[0] for v in sorted_variables] if print_names else '')
