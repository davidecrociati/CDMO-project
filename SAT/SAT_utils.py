from z3 import *

import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

def plot_solution_3d(solution, num_couriers, num_items, num_orders):
    # Create a 3D matrix initialized to 0
    matrix = np.zeros((num_couriers, num_items, num_orders), dtype=int)
    
    # Update the matrix with the solution values
    for (c, i, o) in solution:
        matrix[c][i][o] = 1
    
    fig = plt.figure()
    ax = fig.add_subplot(111, projection='3d')
    
    colors = np.where(matrix == 1, 'green', 'red')
    alpha = np.where(matrix == 1, 0.6, 0.2)
    
    def draw_single_cube(ax, position, color, alpha, value):
        """ Draws a single cube at the given position with the given color and transparency. """
        r = [0, 1]
        vertices = np.array([[x, y, z] for x in r for y in r for z in r])
        vertices = vertices + np.array(position)
        
        faces = [[vertices[j] for j in [0, 1, 3, 2]],
                 [vertices[j] for j in [4, 5, 7, 6]],
                 [vertices[j] for j in [0, 1, 5, 4]],
                 [vertices[j] for j in [2, 3, 7, 6]],
                 [vertices[j] for j in [0, 2, 6, 4]],
                 [vertices[j] for j in [1, 3, 7, 5]]]
        
        ax.add_collection3d(Poly3DCollection(faces, facecolors=color, edgecolors='black', linewidths=0.5, alpha=alpha))
        
        # Add text on top of the cube
        x, y, z = position
        ax.text(x + 0.5, y + 0.5, z + 0.5, str(value), color='black', ha='center', va='center', fontsize=8, weight='bold')

    for c in range(num_couriers):
        for i in range(num_items):
            for o in range(num_orders):
                draw_single_cube(ax, (c, i, o), colors[c, i, o], alpha[c, i, o], matrix[c, i, o])
    
    ax.set_xlabel('Courier')
    ax.set_ylabel('Item')
    ax.set_zlabel('Order')
    ax.set_xticks(range(num_couriers))
    ax.set_yticks(range(num_items))
    ax.set_zticks(range(num_orders))
    
    # Adjust the view and scaling for better visibility
    ax.view_init(elev=20., azim=-35)
    ax.set_box_aspect([num_couriers, num_items, num_orders])  # Aspect ratio is 1:1:1
    
    plt.show()

def print_responsabilities(model, resp):
    s='Responsabilities:\nItems: '
    s+=' '.join(str(i+1) for i in range(len(resp)))+'\n'+'--'*(len(resp)+3)+'\nCour:  '
    for i in range(len(resp)):
        for c in range(len(resp[i])):
            if is_true(model[resp[i][c]]):
                s+=f'{c+1} '
                # break
        # s+='\n'
    print(s)


def display_instance(instance):
    print("num_items:", instance['num_items'])
    print("courier_capacities:", instance['courier_capacities'])
    print("item_sizes:", instance['item_sizes'])
    print("distances:")
    for row in instance['distances']:
        print("  ", row)
    print("lower_bound:", instance['lower_bound'])
    print("upper_bound:", instance['upper_bound'])
    
def print_matrix(matrix, level=0):
    indent = '    ' * level  # indent for each level
    if isinstance(matrix[0], list):  # Check if it's a 2D matrix or higher
        for sub_matrix in matrix:
            if isinstance(sub_matrix[0], list):  # If it's a 3D matrix
                print_matrix(sub_matrix, level + 1)
            else:  # If it's a 2D matrix
                print(indent + '\t'.join(map(str, sub_matrix)))
    else:
        print(indent + '\t'.join(map(str, matrix)))

def print_solution(solution, num_couriers, num_items):
    for courier in range(num_couriers):
        delivered_items = []
        for item in range(num_items):
            for order in range(num_items):
                if (courier, item, order) in solution:
                    delivered_items.append(item)
        if delivered_items:
            print(f"Courier {courier} delivers items: {delivered_items}")
        else:
            print(f"Courier {courier} does not deliver any items.")
            
def delivered_items_list(stops, c, m):
    idxs = []
    for n in range(len(stops[0])) :
        for i in range(len(stops[0][0])) :
            if m.evaluate(stops[c][n][i]) : idxs.append(i)
    return idxs