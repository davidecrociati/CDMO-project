from SAT.constraints import *
from SAT.SAT_utils import *
from z3 import *

def solve(instance_data, MAX_dist, params):
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
    
    # display_instance(instance_data) # for debug
    
    solution = []
    obj = -1
    
    ################################################################################################################
    ## VARIABLES ###################################################################################################
    ################################################################################################################
    num_orders = num_items - (num_couriers -1)  # a courier can't deliver more than n-m items (-1 is due to the courier himself that doesn't count)
    
    stops = [[[Bool(f'stops_{c}_{i}_{o}')   for o in range(num_orders)]         # order of delivering ()
                                            for i in range(num_items)]          # items
                                            for c in range(num_couriers)]       # couriers 

    # TODO: fare due conti per vedere se coviene pre-computare gli ordini oppure no
    #       =>  se è più oneroso portarsi dietro m*n*(n-m) variabili in più 
    #           oppure fare dei cicli in più per le distanze
    # delivered_before = [[[Bool(f'Item_{i}_delivered__before_{j}_by{c}')     for j in range(num_items)]      # item - j
    #                                                                         for i in range(num_items)]      # item - i
    #                                                                         for c in range(num_couriers)]   # courier

    # item_resp = [[Bool(f"delivered_i:{i}_c:{c}") for c in range(num_couriers)]
    #              for i in range(num_items)]

    solver = Solver()
    pars=params.copy()
    if 'timeout' in params:
        pars['timeout'] = int(pars['timeout']*1000) # solver wants timeout in unsigned int milliseconds
        # print(f"SETTO IL TIMEOUT A {pars['timeout']}")
    
    solver.set(**pars)
    
    ################################################################################################################
    ## CONSTRAINTS #################################################################################################
    ################################################################################################################
    
    # 1) Each items must be delivered once
    for i in range(num_items):
        solver.add(exactly_one_seq([stops[c][i][o]
                                    for c in range(num_couriers)
                                    for o in range(num_orders)
                                ], f"item_{i}_delivered_once"))
    
    # 2) Each courrier must deliver at least one item (also structurally guarantted by num_orders)
    for c in range(num_couriers):
        solver.add(at_least_one_seq([stops[c][i][o]
                                    for i in range(num_items)
                                    for o in range(num_orders)
                                ]))
        
    # 3.1) Orders of the items of the same courier must be different unless they are all False
    for c in range(num_couriers):
        for o in range(num_orders):
            # Each courier can deliver at most one item at each order position --> 0 (not delivered item) or 1 (delivered)
            solver.add(at_most_one_seq([stops[c][i][o] 
                                for i in range(num_items)
                                ], f"only_one_item_can_be_delivered_by_{c}_at_order_{o}"))
            
    # 3.2) Orders must be compact
    # so if you deliver 3 items out of 7 you have to have a T in 0, one in 1 and another in 2, not in 6 for examples
    for c in range(num_couriers):
        for o in range(1, num_orders):
            solver.add(Implies(
                Not(Or([stops[c][i][o-1] for i in range(num_items)])),  # If no item delivered at one order
                Not(Or([stops[c][i][o] for i in range(num_items)]))     # then no items delivered in the next order
            ))
    
    # 4) Bin packing : the sum of items sizes must not exceed the max size of the courier
    for c in range(num_couriers):
        solver.add(sum([ If(stops[c][i][o], item_sizes[i], 0)
                        for i in range(num_items)
                        for o in range(num_orders)
                ]) <= courier_capacities[c])
    
    # NOTE : non ha senso farlo perchè a quel punto calcolo direttamente la distanza come faccio dopo
    # FIXME : comunuque NON FUNZIONA
    # # 5) Channeling between stops and delivered_before
    # for c in range(num_couriers) :
    #     for i1 in range(num_couriers) :
    #         for i2 in range(num_couriers) :
    #             if i1 != i2 :
    #                 # If item i2 is delivered rigth after i1
    #                 for o in range(num_orders-1) :
    #                     solver.add(Implies(
    #                         And(stops[c][i1][o], stops[c][i2][o+1]),
    #                         delivered_before[c][i1][i2]
    #                     ))
    
    # 6) Check distances
    # TOT_dist = 226 # per provare sull'istanza
    for c in range(num_couriers) :
        distance_tot = 0
        for i1 in range(num_items): 
            
            # First item
            distance_tot += If(stops[c][i1][0], distances[num_items][i1], 0)
            
            # Middle items
            for i2 in range(num_items):
                if i1 != i2:
                    # If we use delivered_before
                    # distance_tot += If(delivered_before[c][i1][i2], distances[i1][i2], 0)
                    
                    # If we check in place
                    for o in range(num_orders-1) :
                        distance_tot += If(And(
                                            stops[c][i1][o],            # Se i1 è stato consegnato
                                            stops[c][i2][o+1]           # Se i2 è l'ordine dopo i1
                                        ), distances[i1][i2], 0)
            
            # Last item (if the courier filled all his orders)
            distance_tot += If(stops[c][i1][num_orders-1], distances[i1][num_items], 0)
            
            # Last item (if there are empty orders after it)
            for o in range(0, num_orders-1) :
                distance_tot += If(And(                                                             
                        stops[c][i1][o],                                        # If the item is delivered
                        Not(Or([stops[c][j][o+1] for j in range(num_items)]))   # but there aren't delivered items in the next order
                    ), distances[i1][num_items], 0)
            
        solver.add(distance_tot <= MAX_dist)       
    
    ##########################################################################################################
    ## SOLUTION ##############################################################################################
    ##########################################################################################################
    res = solver.check()
    if res == sat:
        m = solver.model()
        sol = [(c, i, o)    for o in range(num_orders)
                            for c in range(num_couriers)
                            for i in range(num_items)
                            if m.evaluate(stops[c][i][o])]

        total_distances = []
        solution = []  # Solution format for SAT_launcher.py
        for c in range(num_couriers):
            delivered_items = []
            for o in range(num_orders):
                for i in range(num_items):
                    if m.evaluate(stops[c][i][o]):
                        delivered_items.append(i)
            solution.append([item+1 for item in delivered_items])
                        

            # DEBUG
            if delivered_items:
                total_size = sum([item_sizes[i] for i in delivered_items ])
                total_distance = distances[num_items][delivered_items[0]]
                total_distance += sum([distances[delivered_items[i - 1]][delivered_items[i]] for i in range(1, len(delivered_items))])
                total_distance += distances[delivered_items[-1]][num_items]  
                total_distances.append(total_distance)
                # print(f"Courier {c} delivers: {solution[c]} --> traveled {total_distance} and loaded {total_size} out of {courier_capacities[c]}")
                
        # obj = max(total_distances)
        return str(res), solution
        # print(f"The longest distance travelled is {obj}") # DEBUG
        # plot_solution_3d(sol, num_couriers, num_items, num_orders) # DEBUG
    else:
        # print("No solution found")
        return 'unsat',None
