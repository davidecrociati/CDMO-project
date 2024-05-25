import sys,os
sys.path.append(os.path.dirname(os.path.dirname(__file__)))
from utils import parse_dzn
import z3

def generate_smt2_model(instance_data):# TODO remove the 14
    # instance_data=parse_dzn(dzn_instance)

    num_couriers = instance_data['num_couriers']
    num_items = instance_data['num_items']
    courier_capacities = instance_data['courier_capacities']
    item_sizes = instance_data['item_sizes']
    distances = instance_data['distances']
    lower_bound = instance_data['lower_bound']
    upper_bound = instance_data['upper_bound']

    # ===== INSTANCE VARIABLES =====
    model_h = f'''
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
    for c, size in enumerate(courier_capacities, start=1):
        model_h += f'(declare-fun courier_{c}_capa () Int)\n'
        model_h += f'(assert (= courier_{c}_capa {size}))\n'
    for i, size in enumerate(item_sizes, start=1):
        model_h += f'(declare-fun item_{i}_size () Int)\n'
        model_h += f'(assert (= item_{i}_size {size}))\n'
    for i in range(num_items+1):
        for j in range(num_items+1):
            model_h += f'(declare-fun distance_{i+1}_{j+1} () Int)\n'
            model_h += f'(assert (= distance_{i+1}_{j+1} {distances[i][j]}))\n'

    # ===== DECISION VARIABLES =====
    for c in range(1,num_couriers+1):
        for i in range(3,num_items+2):
            model_h += f'(declare-fun stop_{c}_{i} () Int)\n'
            model_h += f'(assert (>= stop_{c}_{i} 1))\n'
            model_h += f'(assert (<= stop_{c}_{i} {num_items+1}))\n'
    for i in range(1,num_items+1):
        model_h += f'(declare-fun item_{i}_resp () Int)\n'
        model_h += f'(assert (>= item_{i}_resp 1))\n'
        model_h += f'(assert (<= item_{i}_resp {num_couriers}))\n'
    for c in range(1,num_couriers+1):
        model_h += f'(declare-fun distance_{c}_traveled () Int)\n'
        model_h += f'(assert (>= distance_{c}_traveled 0))\n'
        model_h += f'(assert (<= distance_{c}_traveled {upper_bound}))\n'
    
#     model_h += f'''
# (declare-fun longest_trip () Int)
# (assert (>= longest_trip {lower_bound}))
# (assert (<= longest_trip {upper_bound}))
# '''.lstrip()
    # TODO decomenntare se serve successors
    # for i in range(1,num_items+1):
    #     model_h += f'(declare-fun successors_{i} () Int)\n'
    #     model_h += f'(assert (>= successors_{i} 0))\n'
    #     model_h += f'(assert (<= successors_{i} {num_items+1}))\n'

    # ===== CONSTRAINTS =====
    # bin packing
    # -- declare and calculate couriers load
    # -- loads must not exceed capacities
    for c in range(1,num_couriers+1):
        model_h+=f'(declare-fun load_{c} () Int)\n'
        model_h+=f'(assert (= load_{c} (+'
        for i in range(1,num_items+1):
            model_h+=f'(ite (= item_{i}_resp {c}) item_{i}_size 0)'
        model_h+=')))\n'
        model_h+=f'(assert (<= load_{c} courier_{c}_capa))\n'

    # start and end in depot
    for c in range(1,num_couriers+1):
        model_h += f'(declare-fun stop_{c}_1 () Int)\n'
        model_h += f'(declare-fun stop_{c}_{num_items+2} () Int)\n'
        model_h += f'(assert (= stop_{c}_1 {num_items+1}))\n'
        model_h += f'(assert (= stop_{c}_{num_items+2} {num_items+1}))\n'

    # each courier appears on item resp
    for c in range(1,num_couriers+1):
        model_h+=f'(assert (or '
        for i in range(1,num_items+1):
            model_h+=f'(= item_{i}_resp {c})'
        model_h+='))\n'

    # each couriers must deliver something on 1st stop
    for c in range(1,num_couriers+1):
        model_h += f'(declare-fun stop_{c}_2 () Int)\n'
        model_h += f'(assert (>= stop_{c}_2 1))\n'
        model_h += f'(assert (<= stop_{c}_2 {num_items}))\n'

    # constraint the capacities to be in some sort of order
    for c in range(1,num_couriers):
        model_h+=f'(assert (=> (> courier_{c}_capa courier_{c+1}_capa) (> load_{c} load_{c+1})))'
        # model_h+=f'(assert (=> (< courier_{c}_capa courier_{c+1}_capa) (< load_{c} load_{c+1})))'

    # all items must be delivered. ===LENTO===
    # for i in range(1,num_items+1):
    #     model_h+=f'(assert (= (+'
    #     for c in range(1,num_couriers+1):
    #         for i_ in range(2,num_items+2):
    #             model_h+=f'(ite (= stop_{c}_{i_} {i}) 1 0) '
    #     model_h+=f') 1))'

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
            model_h+=f'(assert (=> {lhs} {rhs}))\n'
            model_h+=f'(assert (=> {rhs} {lhs}))\n'

    # items delivered by c must appear in its row
    for c in range(1,num_couriers+1):
        for i in range(1,num_items+1):
            model_h+=f'(assert (=> (= item_{i}_resp {c}) (or '
            for i_ in range(1,num_items+1):
                model_h+=f'(= stop_{c}_{i_+1} {i})'
            model_h+=f')))\n'

    # define successors
    for i in range(1,num_items+1):
        model_h+=f'(declare-fun successor_of_{i} () Int)\n'
        model_h+=f'(assert (> successor_of_{i} 0))\n'
        model_h+=f'(assert (<= successor_of_{i} {num_items+1}))\n'

    # channeling of successors
    for c in range(1,num_couriers+1):
        for i in range(2,num_items+2):
            for j in range(1,num_items+1):
                # (=> a b c) is (=> a (=> b c))
                # logically a->(b->c)
                A=f'(not (= stop_{c}_{i} {num_items+1}))'
                B=f'(= stop_{c}_{i} {j})'
                C=f'(= successor_of_{j} stop_{c}_{i+1})'
                model_h+=f'(assert (=> {A} {B} {C}))\n'

    # compute distances with successor
    for c in range(1,num_couriers+1):
        model_h+=f'(assert (= distance_{c}_traveled (+ '
        for i in range(1,num_items+1):
            for j in range(1,num_items+2):
                model_h+=f'(ite (and (= item_{i}_resp {c}) (= successor_of_{i} {j}) ) distance_{i}_{j} 0)'
        for j in range(1,num_items+2):
            model_h+=f'(ite (= {j} stop_{c}_2) distance_{num_items+1}_{j} 0)'
        model_h+=f')))\n'

    # compute distances. === ci mette 10 secondi===
    # for c in range(1,num_couriers+1):
    #     model_h+=f'(assert (= distance_{c}_traveled (+ '
    #     for i in range(1,num_items+2):
    #         for j in range(1,num_items+2):
    #             for k in range(1,num_items+2):
    #                 model_h+=f'(ite (and (= stop_{c}_{i} {j})(= stop_{c}_{i+1} {k})) distance_{j}_{k} 0)'
    #     model_h+=f')))\n'
        
    model_t='(check-sat)\n(get-model)'

    return model_h,model_t

def add_objective(num_couriers,obj,head,tail):
    objective=''
    for c in range(1,num_couriers+1):
        # objective+=f'(assert (> distance_{c}_traveled 0))\n'
        objective+=f'(assert (<= distance_{c}_traveled {obj}))\n'
    return head+objective+tail


def parse_solution(model):
    if model==None:
        return []
    # print(model)
    return get_itineraries(model)

def get_itineraries(model):
    stops=get_stops(model,False,False)
    stops=[[int(str(e))for e in row]for row in stops]
    default=stops[0][0]
    stops=[[e for e in row if e!=default]for row in stops ]
    return stops

def get_variables(model,print_names=False):
    get_responsabilities(model,print_names)
    get_loads(model,print_names)
    get_stops(model,print_names)
    get_successor(model,print_names)
    get_distances(model,print_names)

def get_responsabilities(model,print_names):
    variables = []
    for var in model:
        if '_resp' in var.name():
            variables.append((var, model[var]))
    sorted_variables = sorted(variables, key=lambda x: x[0].name())
    print('resp:',[v[1] for v in sorted_variables],[v[0] for v in sorted_variables] if print_names else '')


def get_loads(model,print_names):
    variables = []
    for var in model:
        if 'load_' in var.name():
            variables.append((var, model[var]))
    sorted_variables = sorted(variables, key=lambda x: x[0].name())
    print('loads:',[v[1] for v in sorted_variables],[v[0] for v in sorted_variables] if print_names else '')

def get_stops(model,print_names,print_=True):
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
    if print_:
        print('stops:')
        for i in range(len(matrix)):
            print('  ',matrix[i],matrix_names[i] if print_names else '')
    return matrix

def get_successor(model,print_names):
    variables = []
    for var in model:
        if 'successor' in var.name():
            variables.append((var, model[var]))
    sorted_variables = sorted(variables, key=lambda x: x[0].name())
    print('succ:',[v[1] for v in sorted_variables],[v[0] for v in sorted_variables] if print_names else '')
    
    
def get_distances(model,print_names):
    variables = []
    for var in model:
        if '_traveled' in var.name():
            variables.append((var, model[var]))
    sorted_variables = sorted(variables, key=lambda x: x[0].name())
    print('dists:',[v[1] for v in sorted_variables],[v[0] for v in sorted_variables] if print_names else '')