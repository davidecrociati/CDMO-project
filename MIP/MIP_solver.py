from pulp import *
import time
# install glpk and pulp

def solve(solver, params, data): 
    constraint_loading_time = time.time()
    prob = LpProblem("Multiple_Courier_Planning_Problem", LpMinimize)
    results = set_constraints_Miller_Tucker_Zemlin(prob, data)
    # print('constraint load:',(time.time()-constraint_loading_time),int(time.time()-constraint_loading_time))
    remaining_time = params['timeout']-(time.time()-constraint_loading_time)
    # print('timeout:',remaining_time)
    # solver_list = listSolvers()
    # print(solver_list)
    # solver_list = listSolvers(onlyAvailable=True)
    # print(solver_list)
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
        # OPTIMAL SOLUTION FOUND
        case const.LpSolutionOptimal:
            sol = parse_results(*results)
            return sol, int(prob.objective.value())
        # NOT OPTIMAL SOLUTION FOUND
        case const.LpSolutionIntegerFeasible:
            sol = parse_results(*results)
            return sol, int(prob.objective.value())
        # INFEASIBLE SOLUTION OR NO SOLUTION FOUND OR UNBOUNDED
        case default:
            return [],-1

        
def set_constraints(problem, data):
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


    # remove subtours  ensure that the solution contains no cycles disconnected from the depot
    subtours = []
    for i in range(2,num_items+1):  # generates all combinations of i locations from the total number of locations
        subtours += itertools.combinations(range(num_items), i)
    print(len(subtours))
    for s in subtours:
        # print(s)
        # print(len(s),len(list(itertools.permutations(s,2))))
        problem += lpSum(x[i][j][k] if i !=j else 0 # calculates the total number of edges in the subset s across all couriers
                         for i, j in itertools.permutations(s,2)  # generates all possible directed edges between pairs of locations in subset s
                         for k in range(num_couriers)) <= len(s) - 1    # the total number of edges in any subset s is less than or equal to |s| - 1
                                                                        # 

    return (x, num_couriers, num_items)


def set_constraints_Miller_Tucker_Zemlin(problem, data):
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


    u = LpVariable.dicts("u", [(i, k) for i in range(0, num_items+1) for k in range(num_couriers)], lowBound=0, cat='Continuous')

    # Set the constraints for the MTZ formulation for each courier
    for k in range(num_couriers):
        for i in range(0, num_items):
            for j in range(0, num_items):
                if i != j:
                    problem += u[(i, k)] - u[(j, k)] + 1 <= (num_items-1) * (1-x[i][j][k])

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