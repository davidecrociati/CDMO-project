from pulp import *

def solve(solver, params, data): 
    prob = LpProblem("Multiple Courier Planning Problem",LpMinimize)
    set_constraints(prob, data)
    match solver:
        case 'cbc':
            solve=PULP_CBC_CMD(msg=False,timeLimit= params['timeout'])
        case 'glpk':
            solve=GLPK_CMD(msg=False,timeLimit= params['timeout'])
        case _:
            raise KeyError('Unsupported solver')
    solver.solve(prob)
    
    pass

def set_constraints(prob, data):
    num_couriers = data['num_couriers']
    num_items = data['num_items']
    courier_capacities = data['courier_capacities']
    item_sizes = data['item_sizes']
    distances = data['distances']
    lower_bound = data['lower_bound']
    upper_bound = data['upper_bound']
    
    # Decision variables
    stops = [[LpVariable(name=f'stops{i}_{j}', 
                         cat=LpInteger,
                         lowBound=0,
                         upBound=num_items+1)
              for j in range(num_items)] for i in range(num_couriers)]
    
    # prob += ...
    pass