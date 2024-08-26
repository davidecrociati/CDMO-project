from pulp import *
import time, math
# install glpk and pulp

def solve(solver, params, data): 
    init_time = time.time()
    prob = LpProblem("Multiple_Courier_Planning_Problem", LpMinimize)
    results = set_constraints_Miller_Tucker_Zemlin(prob, data)
    remaining_time = params['timeout']-(time.time()-init_time)
    match solver:
        case 'cbc':
            solver=PULP_CBC_CMD(msg=False, timeLimit=remaining_time)
            # solver = HiGHS_CMD(msg=True, timeLimit=math.ceil(remaining_time))
        case 'glpk':
            solver=GLPK_CMD(msg=True, timeLimit=math.ceil(remaining_time))
        case _:
            raise KeyError('Unsupported solver')
    prob.solve(solver)
    
    opt = False
    solve_time = math.floor(time.time() - init_time)
    sol = []
    obj = -1
    match prob.sol_status:
        # OPTIMAL SOLUTION FOUND
        case const.LpSolutionOptimal:
            sol = parse_results(*results)
            obj = int(prob.objective.value())
            opt = True
        # NOT OPTIMAL SOLUTION FOUND
        case const.LpSolutionIntegerFeasible:
            sol = parse_results(*results)
            obj = int(prob.objective.value())
            opt = False
            solve_time = 300
        # INFEASIBLE SOLUTION OR NO SOLUTION FOUND OR UNBOUNDED
        case default:
            sol = []
            obj =-1
            opt = False
            solve_time = 300
    return sol, obj, opt, solve_time

        
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
        for i in range(num_items):
            for j in range(num_items):
                if i != j:# and item_sizes[i]+item_sizes[j]<=courier_capacities[k]:
                    problem += u[(i, k)] - u[(j, k)] + 1 <= (num_items-1) * (1-x[i][j][k])
        # problem += item_sizes[i]<=u[(i, k)]
        # problem += u[(i, k)]<=courier_capacities[k]

    return (x, num_couriers, num_items)

def set_constraints_Miller_Tucker_Zemlin_2_index(problem, data):
    num_couriers = data['num_couriers']
    num_items = data['num_items']
    courier_capacities = data['courier_capacities']
    item_sizes = data['item_sizes']
    distances = data['distances']
    lower_bound = data['lower_bound']
    upper_bound = data['upper_bound']
    
    # definition of variables which are 0/1
    # courier k do the route from i to j
    x = [[LpVariable("x%s_%s"%(i,j), cat="Binary") if i != j else None for j in range(num_items+1)] for i in range(num_items+1)]

    # add objective function
    longest_trip = LpVariable(name=f'longest', lowBound=lower_bound, upBound=upper_bound, cat=LpInteger)
    problem += lpSum(distances[i][j] * x[i][j] if i != j else 0
                            for i in range(num_items+1) 
                            for j in range (num_items+1))<= longest_trip
    problem += longest_trip
    
    # constraints
    # only one visit per vehicle per item location
    for j in range(num_items):
        problem += lpSum(x[i][j] for i in range(num_items+1) if i != j) == 1 
    for i in range(num_items):
        problem += lpSum(x[i][j] for j in range(num_items+1) if i != j) == 1 

    # depart from the depot and arrival at the depot
    problem += lpSum(x[i][num_items] for i in range(num_items+1)) == num_couriers
    problem += lpSum(x[num_items][j] for j in range(num_items+1)) == num_couriers


    u = [[LpVariable(f"u_{k}_{i}", lowBound=0, upBound=courier_capacities[k], cat="Continuous") for i in range(num_items )] for k in range(num_couriers)]

    for k in range(num_couriers):
        for i in range(num_items ):
            for j in range(num_items):
                if i != j and item_sizes[i]+item_sizes[j]<=courier_capacities[k]:
                    problem += u[k][i] - u[k][j] + courier_capacities[k] * x[i][j] <= courier_capacities[k] - item_sizes[j]

    # Ensure the load variables `u` are consistent with the size of items
    for k in range(num_couriers):
        for i in range(num_items):
            problem += item_sizes[i] <= u[k][i]
            problem += u[k][i] <= courier_capacities[k]

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

def parse_results_2_index(result, num_couriers, num_items):
    for i in range(num_items+1):
        line = ""
        for j in range(num_items+1):
            if i!=j:
                line+=f"{int(result[i][j].value())} "
            else:
                line+="0 "
        print(line)
    res = []
    last_courier_item = 0
    for k in range(num_couriers):
        res.append([])
        end_of_route = False
        i = num_items
        j = last_courier_item

        while not end_of_route:# and j!=num_items:
            if i!=j and result[i][j].value() == 1 and j != num_items:
                if i == num_items:
                    last_courier_item = j+1
                print(f'{k+1} goes from {i+1 if i!=num_items else "D"} to {j+1 if j!=num_items else "D"}')
                res[k].append(j+1)
                i = j
                j = 0
            elif i!=j and result[i][j].value() == 1 and j == num_items:
                print(f'{k+1} goes from {i+1 if i!=num_items else "D"} to {j+1 if j!=num_items else "D"}')
                end_of_route = True
            else:
                j += 1
    return res