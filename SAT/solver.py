from SAT.constraints import *
from SAT.SAT_utils import *
from z3 import *

def solve(instance_data): #, distance):
    '''
    instance data is the dict containing the variables of the 
    dzn file, with the same keys

        returns tuple objective:int,solution:list
    '''
    num_couriers = instance_data['num_couriers']
    num_items = instance_data['num_items']
    courier_capacities = instance_data['courier_capacities']
    item_sizes = instance_data['item_sizes']
    distances = instance_data['distances']
    lower_bound = instance_data['lower_bound']
    upper_bound = instance_data['upper_bound']
    
    display_instance(instance_data) # for debug
    
    solution = []
    obj = -1
    
    ################################################################################################################
    ## VARIABLES ###################################################################################################
    ################################################################################################################
    
    stops = [[[Bool(f'stops_{c}_{i}_{o}')   for o in range(num_items)]      # order of delivering
                                            for i in range(num_items)]      # items
                                            for c in range(num_couriers)]   # couriers 

    delivered_before = [[[Bool(f'delivered_before_{c}_{i}_{j}') for j in range(num_items)]      # item - j
                                                                for i in range(num_items)]      # item - i
                                                                for c in range(num_couriers)]   # courier

    # item_resp = [[Bool(f"delivered_i:{i}_c:{c}") for c in range(num_couriers)]
    #              for i in range(num_items)]

    s = Solver()
    
    ################################################################################################################
    ## CONSTRAINTS #################################################################################################
    ################################################################################################################
    
    # 1) Each items must be delivered once
    for i in range(num_items):
        s.add(exactly_one_seq([stops[c][i][o]
                                    for c in range(num_couriers)
                                    for o in range(num_items)
                                ], f"item_{i}_delivered_once"))
    
    # 2) Each courrier must deliver at least one item
    for c in range(num_couriers):
        s.add(at_least_one_seq([stops[c][i][o]
                                    for i in range(num_items)
                                    for o in range(num_items)
                                ]))
        
    # 3.1) Orders of the items of the same courier must be different unless they are all False
    # for c in range(num_couriers):
    #     for o in range(num_items):
    #         s.add(at_most_one_seq([stops[c][i][o] 
    #                                for i in range(num_items)
    #                             ], f"only_one_item_can_be_delivered_by_{o}"))
    
    # for c in range(num_couriers):
    #     for o in range(num_items):
    #         for i in range(num_items):
    #             for j in range(i + 1, num_items):
    #                 s.add(Or(Not(stops[c][i][o]), Not(stops[c][j][o])))
            
    # 3.2) Orders must be compact
    # so if you deliver 3 items out of 7 you have to have a T in 0, one in 1 and another in 2, not in 6 for examples
    # for c in range(num_couriers) :
    #     for o in range(1, num_items-1) :
    #         s.add(And(
    #             Implies(
    #                 Or([stops[c][i][o] for i in range(num_items)]), 
    #                 Or([stops[c][i][o-1] for i in range(num_items)])), 
    #             Implies(
    #                 Not(Or([stops[c][i][o] for i in range(num_items)])),
    #                 Not(Or([stops[c][i][o+1] for i in range(num_items)])))
    #             ))
    
    # 4) Bin packing : the sum of items sizes must not exceed the max size of the courier
    # for c in range(num_couriers):
    #     s.add(sum([ If(stops[c][i][o], item_sizes[i], 0)
    #                     for i in range(num_items)
    #                     for o in range(num_items)
    #             ]) <= courier_capacities[c])
    
    # 5.1) Channeling between stops and delivered_before
    # for c in range(num_couriers):
    #     for i in range(num_items):
    #         for j in range(num_items):
    #             if i != j:
    #                 # i delivered before j implies that for some order o, stops[c][i][o] is true and stops[c][j][p] is true for p > o
    #                 for o in range(num_items - 1):
    #                     for p in range(o + 1, num_items):
    #                         s.add(Implies(
    #                             And(
    #                                 stops[c][i][o], 
    #                                 stops[c][j][p]
    #                             ), 
    #                             delivered_before[c][i][j]
    #                         ))
    
    # 5.2) Ensure that if `delivered_before[c][i][j]` is true, then `stops[c][i]` must be before `stops[c][j]`
    # for i in range(num_items):
    #     for j in range(num_items):
    #         if i != j:
    #             for o in range(num_items - 1):
    #                 for p in range(o + 1, num_items):
    #                     s.add(Implies(
    #                         delivered_before[c][i][j], 
    #                             And(
    #                                 Not(stops[c][j][o]),
    #                                 stops[c][i][o],
    #                                 stops[c][j][p]
    #                             )
    #                         ))
    
    # 6.1) Collect distances
    # TOT_dist = 14 # per provare sulla prima istanza (optimal = 14)  
    # couriers_distances = []
    # for c in range(num_couriers) :
    #     distance_tot = 0
    #     for i in range(num_items): 
    #         for j in range(num_items):
    #             if i != j:
    #                 distance_tot += If(delivered_before[c][i][j], distances[i][j], 0)

    #     # Include distances from 'home' to the first item and from the last item back to 'home' (in num_items)
    #     for i in range(num_items):
    #         # First item
    #         distance_tot += If(stops[c][i][0], distances[num_items][i], 0)        
            
    #         # Last item
    #         for o in range(1, num_items):
    #             distance_tot += If( 
    #                     And(
    #                         Or([stops[c][j][o-1] for j in range(num_items)]),
    #                         Not(Or([stops[c][j][o] for j in range(num_items)])),
    #                         stops[c][i][o-1]
    #                     ), distances[i][num_items], 0)
            
    #     couriers_distances.append(distance_tot) 
    
    # 6.2) Check distances
    # for c in range(num_couriers):
    #     s.add(And(couriers_distances[c] <= TOT_dist))
    
    ##########################################################################################################
    ## SOLUTION ##############################################################################################
    ##########################################################################################################
    
    if s.check() == sat:
        m = s.model()
        solution = [(c, i, o) for o in range(num_items)
                            for c in range(num_couriers)
                            for i in range(num_items)
                            if m.evaluate(stops[c][i][o])]

        print_solution(solution, num_couriers, num_items)
        plot_solution_3d(solution, num_couriers, num_items)

        total_distances = []
        for c in range(num_couriers):
            # Get the order of delivered items for courier c
            delivered_items = []
            for o in range(num_items):
                for i in range(num_items):
                    if m.evaluate(stops[c][i][o]):
                        delivered_items.append(i)

            if delivered_items:
                # Calculate the total distance for courier c
                total_distance = distances[num_items][delivered_items[0]]  # Home to first item
                total_distance += sum([distances[delivered_items[i - 1]][delivered_items[i]] for i in range(1, len(delivered_items))])
                total_distance += distances[delivered_items[-1]][num_items]  # Last item to home
                total_distances.append(total_distance)

        if total_distances:
            obj = max(total_distances)
            print(f"The longest distance travelled is {obj}")
        else:
            print("No items were delivered.")
    else:
        print("No solution found")
    return obj, solution
