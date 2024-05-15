import itertools

# Define the distance matrix (replace this with your actual distance matrix)
distance_matrix = [
    [0, 4, 6, 7, 2],
    [1, 0, 3, 8, 1],
    [2, 3, 0, 5, 9],
    [3, 2, 5, 0, 6],
    [4, 1, 9, 6, 0]
]

# Define the index corresponding to "Home"
home_index = 4  # Assuming "Home" is the last node

# Generate all permutations of nodes to visit (excluding "Home")
nodes_to_visit = list(range(len(distance_matrix)))
nodes_to_visit.remove(home_index)
all_permutations = itertools.permutations(nodes_to_visit)

# Initialize variables to track the shortest path and its length
shortest_path = None
shortest_distance = float('inf')

# Iterate through all permutations
for perm in all_permutations:
    # Calculate the total distance of the path
    total_distance = distance_matrix[home_index][perm[0]] + distance_matrix[perm[-1]][home_index]
    for i in range(len(perm)-1):
        total_distance += distance_matrix[perm[i]][perm[i+1]]
    
    # Update shortest path if needed
    if total_distance < shortest_distance:
        shortest_distance = total_distance
        shortest_path = [home_index] + list(perm) + [home_index]

# Output the shortest path and its length
print("Shortest Path:", shortest_path)
print("Shortest Distance:", shortest_distance)