from pulp import *
# install glpk and pulp
############################################
# LpSolutionNoSolutionFound = 0
# LpSolutionOptimal = 1
# LpSolutionIntegerFeasible = 2
# LpSolutionInfeasible = -1
# LpSolutionUnbounded = -2
# LpSolution = {
#     LpSolutionNoSolutionFound: "No Solution Found",
#     LpSolutionOptimal: "Optimal Solution Found",
#     LpSolutionIntegerFeasible: "Solution Found",
#     LpSolutionInfeasible: "No Solution Exists",
#     LpSolutionUnbounded: "Solution is Unbounded",
# }
############################################

def solve(solver, params, data): 
    prob = LpProblem("Multiple_Courier_Planning_Problem",LpMinimize)
    result = set_constraints(prob, data)
    match solver:
        case 'cbc':
            solver=PULP_CBC_CMD(msg=False,timeLimit= params['timeout'])
        case 'glpk':
            solver=GLPK_CMD(msg=False,timeLimit= params['timeout'])
        case _:
            raise KeyError('Unsupported solver')
    solver.solve(prob)
    for c in range(result[0]):
        for i in range(result[1]):
            print((result[2][c][i]).value())
    print(prob.sol_status)
    print(prob.status)
    match prob.sol_status:
        # NO SOLUTION FOUND
        case 0:
            return None,-1
        # OPTIMAL SOLUTION FOUND
        case 1:
            return None,-1
        # NOT OPTIMAL SOLUTION FOUND
        case 2:
            return None,-1
        # INFEASIBLE SOLUTION
        case -1:
            return None,-1


def set_constraints(prob, data):
    num_couriers = data['num_couriers']
    num_items = data['num_items']
    courier_capacities = data['courier_capacities']
    item_sizes = data['item_sizes']
    distances = data['distances']
    lower_bound = data['lower_bound']
    upper_bound = data['upper_bound']
    
    # Decision variables
    stops = [[LpVariable(name=f'stops_{i}_{j}', 
                         cat=LpInteger,
                         lowBound=0,
                         upBound=num_items)
              for j in range(num_items)] for i in range(num_couriers)]
    courier_loads = [LpVariable(name=f'courier_loads_{c}', lowBound=0, upBound=courier_capacities[c], cat=LpInteger) for c in range(num_couriers)]
    item_resp = [LpVariable(name=f'item_resp_{i}', lowBound=0, upBound=num_couriers-1, cat=LpInteger) for i in range(num_items)]
    distances_travelled = [LpVariable(name=f'distances_travelled_{c}', lowBound=lower_bound, upBound=upper_bound, cat=LpInteger) for c in range(num_couriers)]
    successors = [LpVariable(name=f'successors_{i}', lowBound=0, upBound=num_items, cat=LpInteger) for i in range(num_items)]
    
    # Objective function
    longest_trip = LpVariable(name=f'longest_trip', lowBound=lower_bound, upBound=upper_bound, cat=LpInteger)
    
    # Define courier loads
    for c in range(num_couriers):
        prob += courier_loads[c] == lpSum(item_sizes[i] for i in range(num_items) if item_resp[i]==c)
        
    # # capacity constraint: the sum of item sizes assigned to each courier must not exceed the courier's capacity
    # for c in range (num_couriers):
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
        
def set_constraints_2(prob, data):
    num_couriers = data['num_couriers']
    num_items = data['num_items']
    courier_capacities = data['courier_capacities']
    item_sizes = data['item_sizes']
    distances = data['distances']
    lower_bound = data['lower_bound']
    upper_bound = data['upper_bound']
        
    for num_couriers in range(1,num_couriers+1):
        
        # definition of LpProblem instance
        problem = pulp.LpProblem("CVRP", pulp.LpMinimize)

        # definition of variables which are 0/1
        x = [[[pulp.LpVariable("x%s_%s,%s"%(i,j,k), cat="Binary") if i != j else None for k in range(num_couriers)]for j in range(num_items)] for i in range(num_items)]

        # add objective function
        problem += pulp.lpSum(distances[i][j] * x[i][j][k] if i != j else 0
                            for k in range(num_couriers) 
                            for j in range(num_items) 
                            for i in range (num_items))

        # constraints
        # formula (2)
        for j in range(1, num_items):
            problem += pulp.lpSum(x[i][j][k] if i != j else 0 
                                for i in range(num_items) 
                                for k in range(num_couriers)) == 1 

        # formula (3)
        for k in range(num_couriers):
            problem += pulp.lpSum(x[0][j][k] for j in range(1,num_items)) == 1
            problem += pulp.lpSum(x[i][0][k] for i in range(1,num_items)) == 1

        # formula (4)
        for k in range(num_couriers):
            for j in range(num_items):
                problem += pulp.lpSum(x[i][j][k] if i != j else 0 
                                    for i in range(num_items)) -  pulp.lpSum(x[j][i][k] for i in range(num_items)) == 0

        #formula (5)
        for k in range(num_couriers):
            problem += pulp.lpSum(df.demand[j] * x[i][j][k] if i != j else 0 for i in range(num_items) for j in range (1,num_items)) <= courier_capacities[k] 


        # fomula (6)
        subtours = []
        for i in range(2,num_items):
            subtours += itertools.combinations(range(1,num_items), i)

        for s in subtours:
            problem += pulp.lpSum(x[i][j][k] if i !=j else 0 for i, j in itertools.permutations(s,2) for k in range(num_couriers)) <= len(s) - 1

        
        # print num_couriers which needed for solving problem
        # print calculated minimum distance value
        if problem.solve() == 1:
            print('Vehicle Requirements:', num_couriers)
            print('Moving Distance:', pulp.value(problem.objective))
            break