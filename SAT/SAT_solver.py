import itertools
from SAT.constraints import *
from SAT.SAT_utils import *
from z3 import *
import time

# 1-HOT encoding on orders (CUBE model)
def solve_hot(instance_data, MAX_dist, params):
    t = time.time()
    
    '''
    instance data is the dict containing the variables of the 
    dzn file, with the same keys

        returns tuple objective:int,solution:list
    '''
    
    ##################################################################################################################################################################
    ## VARIABLES #####################################################################################################################################################
    ##################################################################################################################################################################
    
    num_couriers = instance_data['num_couriers']
    num_items = instance_data['num_items']
    courier_capacities = instance_data['courier_capacities']
    item_sizes = instance_data['item_sizes']
    distances = instance_data['distances']
    
    num_orders = num_items - (num_couriers - 1)  # a courier can't deliver more than n-m items (-1 is due to the courier himself that doesn't count)
    
    stops = [[[Bool(f'stops_{c}_{i}_{o}')   for o in range(num_orders)]         # order of delivering
                                            for i in range(num_items)]          # items
                                            for c in range(num_couriers)]       # couriers 

    solver = Solver()
    
    ##################################################################################################################################################################
    ## CONSTRAINTS ###################################################################################################################################################
    ##################################################################################################################################################################
    
    # print(f"constraint-1 {time.time()-t}")
    # 1) Each items must be delivered once
    for i in range(num_items):
        solver.add(exactly_one_seq([stops[c][i][o]
                                    for c in range(num_couriers)
                                    for o in range(num_orders)
                                ], f"item_{i}_delivered_once"))
    
    # print(f"constraint-2 {time.time()-t}")
    # 2) Each courrier must deliver at least one item (also structurally guarantted by num_orders)
    for c in range(num_couriers):
        solver.add(at_least_one_np([stops[c][i][o]
                                    for i in range(num_items)
                                    for o in range(num_orders)
                                ]))

    # print(f"constraint-3.1 {time.time()-t}")
    # 3.1) Orders of the items of the same courier must be different unless they are all False
    for c in range(num_couriers):
        for o in range(num_orders):
            # Each courier can deliver at most one item at each order position --> 0 (not delivered item) or 1 (delivered)
            solver.add(at_most_one_seq([stops[c][i][o] 
                                for i in range(num_items)
                                ], f"only_one_item_can_be_delivered_by_{c}_at_order_{o}"))
    
    # print(f"constraint-3.2 {time.time()-t}")        
    # 3.2) Orders must be compact
    # so if you deliver 3 items out of 7 you have to have a T in 0, one in 1 and another in 2, not in 6 for examples
    for c in range(num_couriers):
        for o in range(1, num_orders):
            # solver.add(Implies(
            #     Not(Or([stops[c][i][o-1] for i in range(num_items)])),  # If no item delivered at one order
            #     Not(Or([stops[c][i][o] for i in range(num_items)]))     # then no items delivered in the next order
            # ))
            solver.add(Or(
                (Or([stops[c][i][o-1] for i in range(num_items)])),  # If no item delivered at one order
                Not(Or([stops[c][i][o] for i in range(num_items)]))     # then no items delivered in the next order
            ))
    
    # print(f"constraint-4 {time.time()-t}")
    # 4) Bin packing : the sum of items sizes must not exceed the max size of the courier
    for c in range(num_couriers):
        solver.add(sum([ If(stops[c][i][o], item_sizes[i], 0)
                        for i in range(num_items)
                        for o in range(num_orders)
                ]) <= courier_capacities[c])
    
    # print(f"constraint-5 {time.time()-t}")
    # 5) Symmetry breaking: the higher your capacity the higher your load
    for c1 in range(num_couriers):
        for c2 in range(c1+1, num_couriers):
            if courier_capacities[c1] > courier_capacities[c2] :     
                c1_load = sum([ If(stops[c1][i][o], item_sizes[i], 0)                 
                                for i in range(num_items)
                                for o in range(num_orders)])
                c2_load = sum([ If(stops[c2][i][o], item_sizes[i], 0)                 
                                for i in range(num_items)
                                for o in range(num_orders)]) 
                solver.add(c1_load > c2_load)

    # print(f"constraint-6 {time.time()-t}")
    # 6) Check distances
    for c in range(num_couriers) :
        distance_tot = 0
        for i1 in range(num_items): 
            
            # First item
            distance_tot += If(stops[c][i1][0], distances[num_items][i1], 0)
            
            # Last item (if the courier filled all his orders)
            distance_tot += If(stops[c][i1][num_orders-1], distances[i1][num_items], 0)
            
            # Last item (if there are empty orders after it)
            for o in range(0, num_orders-1) :
                distance_tot += If(And(                                                             
                        stops[c][i1][o],                                        # If the item is delivered
                        Not(Or([stops[c][j][o+1] for j in range(num_items)]))   # but there aren't delivered items in the next order
                    ), distances[i1][num_items], 0)
            
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
        solution = []
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
        # print(f"The longest distance travelled is {obj}") # DEBUG
        # plot_solution_3d(sol, num_couriers, num_items, num_orders) # DEBUG
        return 'sat', solution
    else:
        # print("No solution found")
        return 'unsat',[]

# BINARY encoding on orders (CUBE model)
def solve_bin(instance_data, MAX_dist, params):
    t = time.time()
    
    '''
    instance data is the dict containing the variables of the 
    dzn file, with the same keys

        returns tuple objective:int,solution:list
    '''
        
    ##################################################################################################################################################################
    ## VARIABLES #####################################################################################################################################################
    ##################################################################################################################################################################

    num_couriers = instance_data['num_couriers']
    num_items = instance_data['num_items']
    courier_capacities = instance_data['courier_capacities']
    item_sizes = instance_data['item_sizes']
    distances = instance_data['distances']
    
    order_bits = math.ceil(math.log2(num_items - (num_couriers - 1))) + 1       # number of binary digit to represent the max num of orders
                 
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
        solver.add(at_least_one_np([Or(stops[c][i]) for i in range(num_items)]))
        
    # 3) Orders of items for the same courier must be unique and compact
    num_delivered_items = []
    for c in range(num_couriers):
        for i in range(num_items):
            # Uniqueness
            for j in range(i+1, num_items):
                order_i = binary_to_int(stops[c][i], order_bits)
                order_j = binary_to_int(stops[c][j], order_bits)
                solver.add(Implies(And(order_i > 0, order_j > 0), order_i != order_j))
                # solver.add(Or(Not(And(order_i > 0, order_j > 0)), order_i != order_j))
        # Compactness
        num_delivered_items.append(sum([If(Or(stops[c][i]), 1, 0) for i in range(num_items)]))
        total_order_sum = sum([binary_to_int(stops[c][i], order_bits) for i in range(num_items)])
        solver.add(2 * total_order_sum == num_delivered_items[c] * (num_delivered_items[c] + 1)) # Euler formula (restrict and all-different values make it univocal) 
    
    # 4) Bin packing : the sum of items sizes must not exceed the max size of the courier
    for c in range(num_couriers):
        solver.add( sum( [If(Or(stops[c][i]), item_sizes[i], 0) for i in range(num_items)] ) <= courier_capacities[c] )
    
    # 5) Symmetry breaking: the higher your capacity the higher your load
    for c1 in range(num_couriers):
        for c2 in range(c1+1, num_couriers):
            if courier_capacities[c1] > courier_capacities[c2] :
                c1_load = sum([ If(Or(stops[c1][i]), item_sizes[i], 0) for i in range(num_items)])
                c2_load = sum([ If(Or(stops[c2][i]), item_sizes[i], 0) for i in range(num_items)]) 
                solver.add(c1_load > c2_load)
    
    # 6) Check distances
    for c in range(num_couriers) :
        distance_tot = 0
        for i1 in range(num_items): 
            
            # First item
            distance_tot += If( binary_to_int(stops[c][i1], order_bits) ==1 , distances[num_items][i1], 0)
            
            # Last item
            distance_tot += If( binary_to_int(stops[c][i1], order_bits) ==num_delivered_items[c] , distances[i1][num_items], 0)
            
            # Middle items
            order1 = binary_to_int(stops[c][i1], order_bits)
            for i2 in range(i1+1,num_items):
                if i1 != i2:
                # If we use delivered_before
                # distance_tot += If(delivered_before[c][i1][i2], distances[i1][i2], 0)
                    order2 = binary_to_int(stops[c][i2], order_bits)
                    distance_tot += If(And(
                                        Or(stops[c][i1]),
                                        order1 == order2 - 1
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
            
            sol[c] = [item for item, order in courier_deliveries] # for DEBUG format
            solution[c] = [item+1 for item, order in courier_deliveries] # for launcher format
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
        return 'sat', solution
    else:
        # print("No solution found")
        return 'unsat',[]
    
# BINARY encoding on orders (CIRCUIT model)
def solve_circuit(instance_data, MAX_dist, params):
    t = time.time()
    
    '''
    instance data is the dict containing the variables of the 
    dzn file, with the same keys

        returns tuple objective:int,solution:list
    '''
        
    display_instance(instance_data)
        
    ##################################################################################################################################################################
    ## VARIABLES #####################################################################################################################################################
    ##################################################################################################################################################################

    num_couriers = instance_data['num_couriers']
    num_items = instance_data['num_items']
    courier_capacities = instance_data['courier_capacities']
    item_sizes = instance_data['item_sizes']
    distances = instance_data['distances']
    
    successor = [[Bool(f'Item{i}-->Item{j}')    for j in range(num_items)]      
                                                for i in range(num_items)]     
    # Transpose of successor, we use it for better readibility (still the same variables)
    predecessor = [[successor[j][i]             for j in range(num_items)] 
                                                for i in range(num_items)] 
    
    stops = [[Bool(f'Courier_{c}_carries_{i}')  for i in range(num_items)]
                                        for c in range(num_couriers)]    

    solver = Solver()
    
    ##################################################################################################################################################################
    ## CONSTRAINTS ###################################################################################################################################################
    ##################################################################################################################################################################

    # 1) Each items must be delivered once by one courier
    for i in range(num_items):
        # In 'stops', each item has to appear in just one row (courier)
        solver.add(exactly_one_np([stops[c][i] for c in range(num_couriers)], f"{i}_exactly_once_stops"))
    
    # 2) Each courrier must deliver at least one item
    for c in range(num_couriers):
        solver.add(at_least_one_np(stops[c]))
        
    # 3) Item cannot succed itself
    for i in range(num_items) :
        solver.add(Not(successor[i][i]))
        solver.add(Not(predecessor[i][i]))
        
    # 4) Each items must not have more than one successor and one predecessor
    for i in range(num_items):
        solver.add(at_most_one_np(successor[i]))        # successor
        solver.add(at_most_one_np(predecessor[i]))      # predecessor
    
    # 5) An item and its successor must be delivered by the same courier
    for i1 in range(num_items) :
        for i2 in range(num_items) :
            for c in range(num_couriers):
                solver.add(Implies(And(successor[i1][i2], stops[c][i1]), stops[c][i2])) 
                
    # TODO : ROMPERE IL SUBCIRCUIT            
                
            
    # # 6) Break subcircuits
    # # NOTE : If the courier delivers more than 1 item, then there must be 1 first and 1 last item
    # first_items = 0
    # for c in range(num_couriers):
    #     first_items += If(sum([If(stops[c][j], 1, 0) for j in range(num_items)]) > 1, 1, 0)
    # solver.add(And(
    #     # Exactly n first item
    #     sum([If(Not(Or(predecessor[i])), 1, 0) for i in range(num_items)])==first_items,
        
    #     # Exactly n last item
    #     sum([If(Not(Or(successor[i])), 1, 0) for i in range(num_items)])==first_items
    # ))
    
    # # 6) Channeling among stops and successor
    # # NOTE : if the courier delivers more than n>1 items it should appear on successors at least n-1 switches, and it for each courrier
    # # NOTE : forse inutile
    # switch_for_courrier = 0
    # for c in range(num_couriers):
    #     for i in range(num_items):
    #         switch_for_courrier += If(stops[c][i], 1, 0)
    #     switch_for_courrier -= 1 # NOTE there is always at least 1 item delivered so it is general (1 item -> 0 switch)
    # solver.add(sum([If(successor[i][j], 1, 0) for i in range(num_items) for j in range(num_items)])>=switch_for_courrier)

    # 7) Bin packing : the sum of items sizes must not exceed the max size of the courier
    for c in range(num_couriers):
        solver.add(sum([If(stops[c][i], item_sizes[i], 0) for i in range(num_items)]) <= courier_capacities[c])
    
    # 8) Symmetry breaking: the higher your capacity the higher your load
    for c1 in range(num_couriers):
        for c2 in range(c1+1, num_couriers):
            if courier_capacities[c1] > courier_capacities[c2] :     
                c1_load = sum([If(stops[c1][i], item_sizes[i], 0) for i in range(num_items)])
                c2_load = sum([If(stops[c2][i], item_sizes[i], 0) for i in range(num_items)])
                solver.add(c1_load > c2_load)
    
    # # 9) Check distances
    # for c in range(num_couriers):
    #     distance_tot = 0
    #     for i1 in range(num_items):
    #         # First item (has no predecessor)
    #         distance_tot += If(And(
    #                             stops[c][i1],
    #                             Not(Or([successor[j][i1] for j in range(num_items)]))
    #                         ), distances[num_items][i1], 0)
            
    #         # Last item (has no successor)
    #         distance_tot += If(And(
    #                             stops[c][i1],
    #                             Not(Or([successor[i1][j] for j in range(num_items)]))
    #                         ), distances[i1][num_items], 0)
            
    #         # Middle items
    #         for i2 in range(num_items):
    #             if i1!=i2 : distance_tot += If(And(
    #                             stops[c][i1],
    #                             # stops[c][i2], # obvious
    #                             successor[i1][i2]
    #                         ), distances[i1][num_items], 0)
                
    #     solver.add(distance_tot <= MAX_dist)
               
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
        model = solver.model()
        aux = [[] for _ in range(num_couriers)]
        tot_traveled = 0 # DEBUG
        travels = [] # DEBUG
        
        print("#### STOPS ", "#"*40)                            # DEBUG
        print_2D_matrix(stops, model, ax1="C", ax2="I")         # DEBUG
        print("\n\n")
        print("#### SUCCESSOR ", "#"*40)                        # DEBUG
        print_2D_matrix(successor, model, ax1="I_p", ax2="I_s")   # DEBUG
        print("\n\n")
        print("#### PREDECESSOR ", "#"*40)                        # DEBUG
        print_2D_matrix(predecessor, model, ax1="I_s", ax2="I_p")   # DEBUG
        print("\n\n")
        
        for c in range(num_couriers):
            # First item (has no predecessor)
            for i in range(num_items):
                if  model.evaluate(stops[c][i]) and \
                    model.evaluate(Not(Or(predecessor[i]))) : # there is no predecessor
                    print(f"First for {c}: {i}")
                    aux[c].append(i)
                    tot_traveled += distances[num_items][i] # DEBUG
                    
            # Middle items
            for i in range(num_items): 
                for j in range(num_items):
                    if i!=j :
                        if model.evaluate(stops[c][i]) and model.evaluate(successor[i][j]) : 
                            print(f"{i}-->{j}")
                            if i not in aux[c] : aux[c].append(i)
                            tot_traveled += distances[i][j] # DEBUG
                            
             # Last item (has no successor)
            for i in range(num_items):
                if  model.evaluate(stops[c][i]) and \
                    model.evaluate(Not(Or([successor[i][j] for j in range(num_items)]))) : # there is no successor
                        print(f"Last for {c}: {i}")
                        if i not in aux[c] : aux[c].append(i)
                        tot_traveled += distances[i][num_items] # DEBUG
            
            travels.append(tot_traveled)
            
            tot_carry = sum([item_sizes[i] for i in aux[c]]) # DEBUG
            
            # Format the solution (items starts from 1)
            # solution = [[i+1 for i in aux[c]] for c in range(num_couriers)] # well formatted
            solution = [[i for i in aux[c]] for c in range(num_couriers)] # DEBUG
            
            # DEBUG   
            print(f"Courier {c} delivered items {solution[c]} --> carries {tot_carry} out of {courier_capacities[c]} and tarveled {tot_traveled}")
        
        # DEBUG
        print(f"The highest path is {max(travels)}")
        
        return 'sat', solution
    else:
        return 'unsat', []