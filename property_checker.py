import os
import pandas as pd

def matrix_parser(string_matrix):
    rows = [row.strip().split() for row in string_matrix]
    
    matrix = [[] for _ in range(len(rows))]
    
    for i in range(len(rows)):
        for j in range(len(rows[i])):
            matrix[i].append(int(rows[i][j]))
    
    return matrix

def read_file(path):
    result = []
    try:
        with open(path, 'r') as file:
            for line in file:
                line = line.strip()
                result.append(line)
    except FileNotFoundError:
        print(f"Error: File '{path}' not found.")
    except IOError:
        print(f"Error: Unable to read file '{path}'.")
    return result

def transpose(mat, tr, N):
    for i in range(N):
        for j in range(N):
            tr[i][j] = mat[j][i]
  
def check_property(matrix, property):
    match property :
        
        case "simmetry" :
            N = len(matrix)
            tr = [[0 for j in range(len(matrix[0]))] for i in range(len(matrix))]
            transpose(matrix, tr, N)
            for i in range(N):
                for j in range(N):
                    if (matrix[i][j] != tr[i][j]):
                        return False
            return True
            # return matrix == [list(row) for row in zip(*matrix)]
            
        case "triangular-inequality":
            n = len(matrix)
            for i in range(n):
                for j in range(n):
                    for k in range(n):
                        if matrix[i][j] > matrix[i][k] + matrix[k][j]:
                            return False
            return True
        
        case _:
            return "Property not recognized"
            
def check_instances(path_instances_dir, properties):
    results_dict = {"Instance": []}
    for prop in properties:
        results_dict[prop] = []
        
    files = os.listdir(path_instances_dir)
    
    for file in files:
        file_path = os.path.join(path_instances_dir, file)
        
        matrix = matrix_parser(read_file(file_path)[4:])
        not_zeros=min([e for e in r  if e!=0] for r in matrix)
        print(min(not_zeros))
        results = {prop: check_property(matrix, prop) for prop in properties}
        
        results_dict["Instance"].append(file)
        for prop, result in results.items():
            results_dict[prop].append(result)
    
    df = pd.DataFrame(results_dict)
    return df

if __name__ == '__main__' :
    path = 'instances'
    properties = ['simmetry', 'triangular-inequality']
    print(check_instances(path, properties).sort_values(by=['Instance'], ignore_index=True))