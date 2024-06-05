from pulp import *
import time
# install glpk and pulp

def solve(solver, params, data): 
    constraint_loading_time = time.time()
    prob = LpProblem("Multiple_Courier_Planning_Problem", LpMinimize)
    results = set_constraints_2(prob, data)
    # print('constraint load:',(time.time()-constraint_loading_time),int(time.time()-constraint_loading_time))
    remaining_time = int(params['timeout']-(time.time()-constraint_loading_time))
    # print('timeout:',remaining_time)
    match solver:
        case 'cbc':
            solver=PULP_CBC_CMD(msg=False, timeLimit=remaining_time)
        case 'glpk':
            solver=GLPK_CMD(msg=False, timeLimit=remaining_time)
        case _:
            raise KeyError('Unsupported solver')
    
    constraint_loading_time = time.time()
    prob.solve(solver)
    # print('solving time:', (time.time()-constraint_loading_time),int(time.time()-constraint_loading_time))
    # print('solution time:', prob.solutionTime)
    match prob.sol_status:
        # NO SOLUTION FOUND
        case 0:
            return [],-1
        # OPTIMAL SOLUTION FOUND
        case 1:
            sol = parse_results(*results)
            return sol, int(prob.objective.value())
        # NOT OPTIMAL SOLUTION FOUND
        case 2:
            sol = parse_results(*results)
            return sol, int(prob.objective.value())
        # INFEASIBLE SOLUTION
        case -1:
            return [],-1


def set_constraints(prob, data):
    # num_couriers = data['num_couriers']
    # num_items = data['num_items']
    # courier_capacities = data['courier_capacities']
    # item_sizes = data['item_sizes']
    # distances = data['distances']
    # lower_bound = data['lower_bound']
    # upper_bound = data['upper_bound']
    
    # # Decision variables
    # stops = [[LpVariable(name=f'stops_{c}_{i}', 
    #                      cat=LpInteger,
    #                      lowBound=0,
    #                      upBound=num_items)
    #           for i in range(num_items)] for c in range(num_couriers)]
    # courier_loads = [LpVariable(name=f'courier_loads_{c}', lowBound=0, upBound=courier_capacities[c], cat=LpInteger) for c in range(num_couriers)]
    # item_resp = [LpVariable(name=f'item_resp_{i}', lowBound=0, upBound=num_couriers-1, cat=LpInteger) for i in range(num_items)]
    # distances_travelled = [LpVariable(name=f'distances_travelled_{c}', lowBound=lower_bound, upBound=upper_bound, cat=LpInteger) for c in range(num_couriers)]
    # successors = [LpVariable(name=f'successors_{i}', lowBound=0, upBound=num_items, cat=LpInteger) for i in range(num_items)]
    
    # # Objective function
    # longest_trip = LpVariable(name=f'longest_trip', lowBound=lower_bound, upBound=upper_bound, cat=LpInteger)
    # prob += longest_trip
    # Bin packing constraint: the sum of item sizes assigned to each courier must not exceed the courier's capacity
    # for c in range(num_couriers):
    #     prob += lpSum(item_sizes[i] for i in range(num_items) if item_resp[i]==c) == courier_loads[c]
    #     prob += courier_loads[c] <= courier_capacities[c]
        
 
    # # each courier must be responsible for delivering at least one item
    # for c in range(num_couriers):
    #     prob += lpSum(item_resp[i] == c for i in range(num_items)) >= 1
    
    # # each courier have to stop in at least one location different from the depot
    # for c in range(num_couriers):
    #     prob += stops[c][0] <= num_items+1
        
    # # all items must be delivered
    # for i in range(num_items):
    #     prob += lpSum(stops[c][i2]==i for c in range(num_couriers) for i2 in range(num_items)) == 1
    
    # # Channeling constraint
    # for c in range(num_couriers):
    #     pass
    
    return (num_couriers,
            num_items,
            stops,
            courier_loads,
            item_resp,
            distances_travelled,
            successors,
            longest_trip)
        
        
def set_constraints_2(problem, data):
    num_couriers = data['num_couriers']
    num_items = data['num_items']
    courier_capacities = data['courier_capacities']
    item_sizes = data['item_sizes']
    distances = data['distances']
    lower_bound = data['lower_bound']
    upper_bound = data['upper_bound']
    
    # definition of variables which are 0/1
    # courier k do the route from i to j
    x = [[[LpVariable("x%s_%s,%s"%(i,j,k), cat="Binary") if i != j else None for k in range(num_couriers)]for j in range(num_items+1)] for i in range(num_items+1)]

    # add objective function
    longest_trip = LpVariable(name=f'longest', lowBound=lower_bound, upBound=upper_bound, cat=LpInteger)
    for k in range(num_couriers):
        problem += lpSum(distances[i][j] * x[i][j][k] if i != j else 0
                            for j in range(num_items+1) 
                            for i in range (num_items+1))<= longest_trip
    problem += longest_trip
    
    # constraints
    # only one visit per vehicle per item location
    for j in range(num_items):
        problem += lpSum(x[i][j][k] if i != j else 0 
                            for i in range(num_items+1) 
                            for k in range(num_couriers)) == 1 

    # depart from the depot and arrival at the depot
    for k in range(num_couriers):
        problem += lpSum(x[num_items][j][k] for j in range(num_items)) == 1
        problem += lpSum(x[i][num_items][k] for i in range(num_items)) == 1

    # the number of vehicles coming in and out of a item location is the same
    for k in range(num_couriers):
        for j in range(num_items+1):
            problem += lpSum(x[i][j][k] if i != j else 0 
                                for i in range(num_items+1)) -  lpSum(x[j][i][k] for i in range(num_items+1)) == 0

    # the delivery capacity of each vehicle should not exceed the maximum capacity
    for k in range(num_couriers):
        problem += lpSum(item_sizes[j] * x[i][j][k] if i != j else 0 for i in range(num_items+1) for j in range (num_items)) <= courier_capacities[k] 


    # remove subtours
    subtours = []
    for i in range(2,num_items+1):
        subtours += itertools.combinations(range(num_items), i)
    for s in subtours:
        problem += lpSum(x[i][j][k] if i !=j else 0 for i, j in itertools.permutations(s,2) for k in range(num_couriers)) <= len(s) - 1

    return (x, num_couriers, num_items)


def parse_results(result, num_couriers, num_items):
    
    res = []
    for k in range(num_couriers):
        res.append([])
        end_of_route = False
        i = num_items
        j = 0
        while not end_of_route:
            if i!=j and result[i][j][k].value() == 1 and j != num_items:
                # print(f'{k+1} goes from {i+1 if i!=num_items else "D"} to {j+1 if j!=num_items else "D"}')
                res[k].append(j+1)
                i = j
                j = 0
            elif i!=j and result[i][j][k].value() == 1 and j == num_items:
                # print(f'{k+1} goes from {i+1 if i!=num_items else "D"} to {j+1 if j!=num_items else "D"}')
                end_of_route = True
            else:
                j += 1
    return res