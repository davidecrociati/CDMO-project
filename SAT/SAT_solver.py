from SAT.constraints import *
from SAT.SAT_utils import *
from z3 import *
import time

# NUMERICAL APPROACH ON ORDERS (FIXME : forse ancora ottimizzabile)
def solve(instance_data, MAX_dist, params):
    t = time.time()
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
    # lower_bound = instance_data['lower_bound']
    # upper_bound = instance_data['upper_bound']
    
    # display_instance(instance_data) # for debug
    
    solution = []  # Solution format for SAT_launcher.py
    obj = -1
    
    ##################################################################################################################################################################
    ## VARIABLES #####################################################################################################################################################
    ##################################################################################################################################################################
    
    num_orders = num_items - (num_couriers - 1)  # a courier can't deliver more than n-m items (-1 is due to the courier himself that doesn't count)
                                                 # => WE USE num_items * (num_couriers - 1) LESS VARIABLES [than putting num_orders=num_items]
    
    stops = [[[Bool(f'stops_{c}_{i}_{o}')   for o in range(num_orders)]         # order of delivering
                                            for i in range(num_items)]          # items
                                            for c in range(num_couriers)]       # couriers 

    solver = Solver()
    
    ##################################################################################################################################################################
    ## CONSTRAINTS ###################################################################################################################################################
    ##################################################################################################################################################################
    
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
    
    # 5) Symmetry breaking: 
    for c1 in range(num_couriers):
        for c2 in range(num_couriers):
            if c1!=c2 and courier_capacities[c1] > courier_capacities[c2] :     # If the courier c1 has a bigger capacity than courier c2
                solver.add(
                    sum([ If(stops[c1][i][o], item_sizes[i], 0)                 # Then he sum of all the sizes of the item brought by the courier c1
                        for i in range(num_items)
                        for o in range(num_orders)]) 
                    >                                                           # must be greater than
                    sum([ If(stops[c2][i][o], item_sizes[i], 0)                 # Then he sum of all the sizes of the item brought by the courier c2
                        for i in range(num_items)
                        for o in range(num_orders)]) 
                )
                
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
    
    ############################################################################################################################################################
    ## SOLUTION ################################################################################################################################################
    ############################################################################################################################################################
    
    pars=params.copy()
    load_time = time.time()-t
    # print(f"Ci ha messo {load_time} secondi a caricare i constraint")
    if 'timeout' in params:
        # We have to consider the constraint loading time in the timer
        if load_time > pars['timeout'] : pars['timeout']=load_time # exit immediatly
        pars['timeout'] = int((pars['timeout']-load_time)*1000) 
    solver.set(**pars, random_seed=42)
    
    res = solver.check()

    if res == sat:
        m = solver.model()
        
        sol = [(c, i, o)    for o in range(num_orders)
                            for c in range(num_couriers)
                            for i in range(num_items)
                            if m.evaluate(stops[c][i][o])]

        total_distances = []
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
        return 'unsat',solution

# BINARY APPROACH ON ORDERS (FIXME : forse ancora ottimizzabile)
def solve_bin(instance_data, MAX_dist, params):
    t = time.time()
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
    # lower_bound = instance_data['lower_bound']
    # upper_bound = instance_data['upper_bound']
    
    # display_instance(instance_data) # for debug
    
    solution = []  # Solution format for SAT_launcher.py
    obj = -1
    
    ##################################################################################################################################################################
    ## VARIABLES #####################################################################################################################################################
    ##################################################################################################################################################################
    
    order_bits = math.ceil(math.log2(num_items - (num_couriers - 1))) + 1 # number of binary digit to represent the max num of orders
                 
    stops = [[[Bool(f'stops_{c}_{i}_{b}')   for b in range(order_bits)]         # order of delivering
                                            for i in range(num_items)]          # items
                                            for c in range(num_couriers)]       # couriers 

    solver = Solver()
    
    ##################################################################################################################################################################
    ## CONSTRAINTS ###################################################################################################################################################
    ##################################################################################################################################################################
    
    # 1) Each items must be delivered once
    # NOTE: An item is delivered if it has an encoding different from 0 --> if Or(encoding)=1
    for i in range(num_items):
        solver.add(exactly_one_bw([Or(stops[c][i]) for c in range(num_couriers)], f"item_{i}_delivered_once"))
    
    # 2) Each courrier must deliver at least one item (also structurally guarantted by num_orders)
    # NOTE: An item is delivered if it has an encoding different from 0 --> if Or(encoding)=1
    for c in range(num_couriers):
        solver.add(at_least_one_bw([Or(stops[c][i]) for i in range(num_items)]))
        
    # 3.1) Orders of the items of the same courier must be different unless they are all 0s
    for c in range(num_couriers):
        for i in range(num_items):
            for j in range(i+1, num_items):
                # Create integer representations of the orders
                order_i = sum([If(stops[c][i][b], 2**b, 0) for b in range(order_bits)]) 
                order_j = sum([If(stops[c][j][b], 2**b, 0) for b in range(order_bits)]) 
                
                # If both items are delivered, their orders must be different
                solver.add(Implies(
                        And(order_i > 0, order_j > 0), 
                        order_i != order_j
                    ))
            
    # 3.2) Orders must be compact
    # This means that i have use all the orders possible in the range(1, max(order_used)), so that there are no gaps
    num_delivered_items = [0 for _ in range(num_couriers)] # we'll need it for distances
    for c in range(num_couriers) :
        tot = 0 
        for i in range(num_items) :
            num_delivered_items[c] += If(Or(stops[c][i]), 1, 0) # orders mus be in [1, num_delivered_items] --> their sum must be num_delivered_items*(num_delivered_items+1)/2 (Euler)
            tot +=  sum([If(stops[c][i][b], 2**b, 0) for b in range(order_bits)])
        solver.add( (2*tot) == (num_delivered_items[c] * (num_delivered_items[c] + 1)) ) # rearranging Euler for avoid divisions    
    
    # 4) Bin packing : the sum of items sizes must not exceed the max size of the courier
    for c in range(num_couriers):
        solver.add( sum( [If(Or(stops[c][i]), item_sizes[i], 0) for i in range(num_items)] ) <= courier_capacities[c] )
    
    # 5) Symmetry breaking: 
    for c1 in range(num_couriers):
        for c2 in range(c1+1, num_couriers):
            if courier_capacities[c1] > courier_capacities[c2] :     # If the courier c1 has a bigger capacity than courier c2
                solver.add(
                    sum([ If(Or(stops[c1][i]), item_sizes[i], 0)                 # Then he sum of all the sizes of the item brought by the courier c1
                        for i in range(num_items)]) 
                    >                                                            # must be greater than
                    sum([ If(Or(stops[c2][i]), item_sizes[i], 0)                 # Then he sum of all the sizes of the item brought by the courier c2
                        for i in range(num_items)]) 
                )
                
    
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
    for c in range(num_couriers) :
        distance_tot = 0
        for i1 in range(num_items): 
            
            # First item
            distance_tot += If( sum([If(stops[c][i1][b], 2**b, 0) for b in range(order_bits)])==1 , distances[num_items][i1], 0)
            
            # Last item
            distance_tot += If( sum([If(stops[c][i1][b], 2**b, 0) for b in range(order_bits)])==num_delivered_items[c] , distances[i1][num_items], 0)
            
            # Middle items
            for i2 in range(num_items):
                if i1 != i2:
                # If we use delivered_before
                # distance_tot += If(delivered_before[c][i1][i2], distances[i1][i2], 0)
                
                    distance_tot += If(And(
                                        Or(stops[c][i1]),
                                        sum([If(stops[c][i1][b], 2**b, 0) for b in range(order_bits)]) == (sum([If(stops[c][i2][b], 2**b, 0) for b in range(order_bits)]) - 1)
                                    ), distances[i1][i2], 0)
            
        solver.add(distance_tot <= MAX_dist)       
    
    ############################################################################################################################################################
    ## SOLUTION ################################################################################################################################################
    ############################################################################################################################################################
    
    pars=params.copy()
    load_time = time.time()-t
    # print(f"Ci ha messo {load_time} secondi a caricare i constraint")
    if 'timeout' in params:
        # We have to consider the constraint loading time in the timer
        if load_time > pars['timeout'] : pars['timeout']=load_time # exit immediatly
        pars['timeout'] = int((pars['timeout']-load_time)*1000) 
    solver.set(**pars, random_seed=42)
    
    res = solver.check()

    if res == sat:
        m = solver.model()
        solution = [[] for _ in range(num_couriers)]  # Initialize a list of lists for each courier
        sol = [[] for _ in range(num_couriers)]  # Initialize a list of lists for each courier
        total_distances = []
        
        for c in range(num_couriers):
            courier_deliveries = []
            for i in range(num_items):
                order_bin = ''.join(['1' if is_true(m.evaluate(stops[c][i][b])) else '0' for b in reversed(range(order_bits))])
                order = int(order_bin, 2)  # Convert binary string to decimal
                if order > 0:  # If order is 0, it means the item is not delivered by this courier
                    courier_deliveries.append((i, order))
                # print(f"Courier {c} delivered item {i} as {order} encoded as {order_bin} ({[f"b_{b}" for b in reversed(range(order_bits))]})")
            
            # Sort items for this courier by order
            courier_deliveries.sort(key=lambda x: x[1])
            
            # Append sorted items (only item indices) to the sol list for this courier
            sol[c] = [item for item, order in courier_deliveries]
            # for launcher format
            solution[c] = [item+1 for item, order in courier_deliveries]
            # print(f"\nCourier {c} delivers items in order: {solution[c]}")

            # DEBUG
            if sol[c]:
                total_size = sum([item_sizes[i] for i in sol[c] ])
                total_distance = distances[num_items][sol[c][0]]
                total_distance += sum([distances[sol[c][i - 1]][sol[c][i]] for i in range(1, len(sol[c]))])
                total_distance += distances[sol[c][-1]][num_items]  
                total_distances.append(total_distance)
                # print(f"Courier {c} delivers: {solution[c]} --> traveled {total_distance} and loaded {total_size} out of {courier_capacities[c]}")
            
        
        # plot_solution_3d(sol, num_couriers, num_items, order_bits) # DEBUG
        
        obj = max(total_distances)
        # print(f"The longest distance travelled is {obj}") # DEBUG
        return str(res), solution
    else:
        # print("No solution found")
        return 'unsat',solution
















# TODO : ma anche questo sembrerebbe inutile visto che è chiamato solo da launch che è deprecato
# def solve_pelle(instance_data, MAX_dist, params):
#     '''
#     instance data is the dict containing the variables of the 
#     dzn file, with the same keys

#         returns tuple objective:int,solution:list
#     '''
#     num_couriers = instance_data['num_couriers']
#     num_items = instance_data['num_items']
#     courier_capacities = instance_data['courier_capacities']
#     item_sizes = instance_data['item_sizes']
#     distances = instance_data['distances']
#     lower_bound = instance_data['lower_bound']
#     upper_bound = instance_data['upper_bound']
    
#     display_instance(instance_data) # for debug
    
#     solution = []
#     obj = -1
    
#     ################################################################################################################
#     ## VARIABLES ###################################################################################################
#     ################################################################################################################
#     num_orders = num_items - (num_couriers -1)  # a courier can't deliver more than n-m items (-1 is due to the courier himself that doesn't count)
    
#     stops = [[[Bool(f'stops_{c}_{i}_{o}')   for o in range(num_orders)]         # order of delivering ()
#                                             for i in range(num_items)]          # items
#                                             for c in range(num_couriers)]       # couriers 

#     # TODO: fare due conti per vedere se coviene pre-computare gli ordini oppure no
#     #       =>  se è più oneroso portarsi dietro m*n*(n-m) variabili in più 
#     #           oppure fare dei cicli in più per le distanze
#     # delivered_before = [[[Bool(f'Item_{i}_delivered__before_{j}_by{c}')     for j in range(num_items)]      # item - j
#     #                                                                         for i in range(num_items)]      # item - i
#     #                                                                         for c in range(num_couriers)]   # courier

#     # item_resp = [[Bool(f"delivered_i:{i}_c:{c}") for c in range(num_couriers)]
#     #              for i in range(num_items)]

#     s = Solver()
#     pars=params.copy()
#     if 'timeout' in params:
#         pars['timeout'] = int(pars['timeout']*1000) # solver wants timeout in unsigned int milliseconds
    
#     print(f"SETTO IL TIMEOUT A {pars['timeout']}")
#     s.set(**pars)
    
#     ################################################################################################################
#     ## CONSTRAINTS #################################################################################################
#     ################################################################################################################
    
#     # 1) Each items must be delivered once
#     for i in range(num_items):
#         s.add(exactly_one_seq([stops[c][i][o]
#                                     for c in range(num_couriers)
#                                     for o in range(num_orders)
#                                 ], f"item_{i}_delivered_once"))
    
#     # 2) Each courrier must deliver at least one item (also structurally guarantted by num_orders)
#     for c in range(num_couriers):
#         s.add(at_least_one_seq([stops[c][i][o]
#                                     for i in range(num_items)
#                                     for o in range(num_orders)
#                                 ]))
        
#     # 3.1) Orders of the items of the same courier must be different unless they are all False
#     for c in range(num_couriers):
#         for o in range(num_orders):
#             # Each courier can deliver at most one item at each order position --> 0 (not delivered item) or 1 (delivered)
#             s.add(at_most_one_seq([stops[c][i][o] 
#                                 for i in range(num_items)
#                                 ], f"only_one_item_can_be_delivered_by_{c}_at_order_{o}"))
            
#     # 3.2) Orders must be compact
#     # so if you deliver 3 items out of 7 you have to have a T in 0, one in 1 and another in 2, not in 6 for examples
#     for c in range(num_couriers):
#         for o in range(1, num_orders):
#             s.add(Implies(
#                 Not(Or([stops[c][i][o-1] for i in range(num_items)])),  # If no item delivered at one order
#                 Not(Or([stops[c][i][o] for i in range(num_items)]))     # then no items delivered in the next order
#             ))
    
#     # 4) Bin packing : the sum of items sizes must not exceed the max size of the courier
#     for c in range(num_couriers):
#         s.add(sum([ If(stops[c][i][o], item_sizes[i], 0)
#                         for i in range(num_items)
#                         for o in range(num_orders)
#                 ]) <= courier_capacities[c])
    
#     # NOTE : non ha senso farlo perchè a quel punto calcolo direttamente la distanza come faccio dopo
#     # FIXME : comunuque NON FUNZIONA
#     # # 5) Channeling between stops and delivered_before
#     # for c in range(num_couriers) :
#     #     for i1 in range(num_couriers) :
#     #         for i2 in range(num_couriers) :
#     #             if i1 != i2 :
#     #                 # If item i2 is delivered rigth after i1
#     #                 for o in range(num_orders-1) :
#     #                     s.add(Implies(
#     #                         And(stops[c][i1][o], stops[c][i2][o+1]),
#     #                         delivered_before[c][i1][i2]
#     #                     ))
    
#     # 6) Check distances
#     # TOT_dist = 226 # per provare sull'istanza
#     for c in range(num_couriers) :
#         distance_tot = 0
#         for i1 in range(num_items): 
            
#             # First item
#             distance_tot += If(stops[c][i1][0], distances[num_items][i1], 0)
            
#             # Middle items
#             for i2 in range(num_items):
#                 if i1 != i2:
#                     # If we use delivered_before
#                     # distance_tot += If(delivered_before[c][i1][i2], distances[i1][i2], 0)
                    
#                     # If we check in place
#                     for o in range(num_orders-1) :
#                         distance_tot += If(And(
#                                             stops[c][i1][o],            # Se i1 è stato consegnato
#                                             stops[c][i2][o+1]           # Se i2 è l'ordine dopo i1
#                                         ), distances[i1][i2], 0)
            
#             # Last item (if the courier filled all his orders)
#             distance_tot += If(stops[c][i1][num_orders-1], distances[i1][num_items], 0)
            
#             # Last item (if there are empty orders after it)
#             for o in range(0, num_orders-1) :
#                 distance_tot += If(And(                                                             
#                         stops[c][i1][o],                                        # If the item is delivered
#                         Not(Or([stops[c][j][o+1] for j in range(num_items)]))   # but there aren't delivered items in the next order
#                     ), distances[i1][num_items], 0)
            
#         s.add(distance_tot <= MAX_dist)       
    
#     ##########################################################################################################
#     ## SOLUTION ##############################################################################################
#     ##########################################################################################################
#     res = s.check()
#     if res == sat:
#         m = s.model()
#         sol = [(c, i, o)    for o in range(num_orders)
#                             for c in range(num_couriers)
#                             for i in range(num_items)
#                             if m.evaluate(stops[c][i][o])]

#         total_distances = []
#         solution = []  # Solution format for SAT_launcher.py
#         for c in range(num_couriers):
#             delivered_items = []
#             for o in range(num_orders):
#                 for i in range(num_items):
#                     if m.evaluate(stops[c][i][o]):
#                         delivered_items.append(i)
#             solution.append([item+1 for item in delivered_items])
                        

#             # DEBUG
#             if delivered_items:
#                 total_size = sum([item_sizes[i] for i in delivered_items ])
#                 total_distance = distances[num_items][delivered_items[0]]
#                 total_distance += sum([distances[delivered_items[i - 1]][delivered_items[i]] for i in range(1, len(delivered_items))])
#                 total_distance += distances[delivered_items[-1]][num_items]  
#                 total_distances.append(total_distance)
#                 print(f"Courier {c} delivers: {solution[c]} --> traveled {total_distance} and loaded {total_size} out of {courier_capacities[c]}")
                
#         obj = max(total_distances)
#         print(f"The longest distance travelled is {obj}") # DEBUG
#         # plot_solution_3d(sol, num_couriers, num_items, num_orders) # DEBUG
#     else:
#         print("No solution found")
#     return str(res), (obj, solution)
