from SAT.constraints import *
from z3 import *


def solve(instance_data):
    '''
    instance data is the dict containing the variables of the 
    dzn file, with the same keys

        returns tuple objective:int,solution:list
    '''
    num_couriers = instance_data['num_couriers']
    num_items = instance_data['num_items']
    courier_sizes = instance_data['courier_sizes']
    item_sizes = instance_data['item_sizes']
    distances = instance_data['distances']
    lower_bound = instance_data['lower_bound']
    upper_bound = instance_data['upper_bound']

    solution = []
    obj = -1

    # setting up the variables
    # stops = [[[Bool(f'stops_{c}_{s}_{i}') for i in range(num_items+1)]
    #         for s in range(num_items+2)] for c in range(num_couriers)]
    item_resp = [[Bool(f"delivers_{i}_{c}") for c in range(num_couriers)] for i in range(num_items)]
    # distances_traveled=[] # distance traveled by each courier
    # longest_trip=lower_bound # init it to lower bound
    # assert longest_trip<=upper_bound # and bound it 

    s = Solver()

    s.add(AtMost(*([item_resp[i][c]] for i in range(num_items) for c in range(num_couriers)),2))
    # adding the constraints
    # print(courier_sizes,item_resp,item_sizes)
    # s.add(bin_packing(courier_sizes,item_resp,item_sizes))
    print(s.check())
    s.check()
    m=s.model()
    print(m.evaluate(item_resp[0][0]))
    delivers=[(i,c) for i in range(num_items) for c in range(num_couriers) if m.evaluate(item_resp[i][c])]
    print(delivers)
    # look for solutions
    # for objective in range(lower_bound,upper_bound+1):
    #     # impose to solve for objective
    #     if s.check==sat:
    #         obj=objective
    #         m=s.model()
    #         solution=str(m) # assign the solution somehow, maybe with `m`
    #         break

    # if s.check()!=sat:
    #     obj='unsat'

    return obj, solution
