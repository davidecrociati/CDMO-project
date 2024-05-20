from z3 import *

# Function to define the bin packing problem constraints using Boolean variables
def bin_packing(c, bin_vars, w):
    num_items = len(w)
    num_bins = len(c)
    
    constraints = []

    # Constraint: each item must be assigned to exactly one bin
    for i in range(num_items):
        constraints.append(Sum([If(bin_vars[i][b], 1, 0) for b in range(num_bins)]) == 1)

    # Constraint: the capacity of each bin must not be exceeded
    for b in range(num_bins):
        constraints.append(Sum([If(bin_vars[i][b], w[i], 0) for i in range(num_items)]) <= c[b])

    return constraints

# Example usage
c = [10, 15]  # Capacities of the bins
w = [2, 3, 5, 7, 1]  # Weights of the items
num_items = len(w)
num_bins = len(c)

# Boolean variables representing whether item i is in bin b
bin_vars = [[Bool(f'item_{i}_bin_{b}') for b in range(num_bins)] for i in range(num_items)]

# Creating the solver
s = Solver()

# Add the bin packing constraints to the solver
s.add(bin_packing(c, bin_vars, w))

# Check if a solution exists
if s.check() == sat:
    model = s.model()
    print("Solution found:")
    for i in range(num_items):
        for b in range(num_bins):
            if is_true(model[bin_vars[i][b]]):
                print(f'Item {i} is in bin {b}')
else:
    print("No solution exists")
