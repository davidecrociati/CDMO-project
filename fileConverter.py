import os

def insert_commas(string:str):
    '''
	From a string in the form '2 3 4 3 4 4 0' returns a single string '2, 3, 4, 3, 4, 4, 0'
    '''
    elements = string.split()
    formatted_string = ", ".join(elements)
    return formatted_string

def matrix_parser(string_matrix):
    rows = [row.strip().split() for row in string_matrix]
    
    matrix = [[] for _ in range(len(rows))]
    
    for i in range(len(rows)):
        for j in range(len(rows[i])):
            matrix[i].append(int(rows[i][j]))
    
    return matrix

def find_upper_bound(data):
    return sum([max(r) for r in data])

def find_lower_bound(data):
    return 0

def write_new_content(data):
    content = ''
    bounds = matrix_parser(data[4:]) 
    
    content += 'num_couriers='+data[0]+';\n'
    content += 'num_items='+data[1]+';\n'
    content += 'courier_sizes=['+insert_commas(data[2])+'];\n'
    content += 'item_sizes=['+insert_commas(data[3])+'];\n'
    content += 'distances=['
    for table_row in data[4:]:
        content+='|'+insert_commas(table_row)+'\n'
    content=content[:-1]
    content+='|];\n'
    content += 'lower_bound='+str(find_lower_bound(bounds))+';\n'
    content += 'upper_bound='+str(find_upper_bound(bounds))+';\n'
    return content

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


def save_dzn_file(filename, content):
    with open(filename+'.dzn', 'w') as file:
        file.write(content)

if __name__=='__main__':

    script_dir = os.path.dirname(os.path.abspath(__file__))

    os.chdir(script_dir)

    instances_folder = "instances"
    DZN_instances_folder = "instances_dzn"
    os.makedirs(DZN_instances_folder, exist_ok=True)
    file_names = os.listdir(instances_folder)
        
    for file_name in file_names:
        if file_name.endswith(".dat"):
            file_path = os.path.join(instances_folder, file_name)

            data=read_file(file_path)
            formatted_data=write_new_content(data)

            dzn_file_name=DZN_instances_folder+'/'+file_name[:-4]
            save_dzn_file(dzn_file_name,formatted_data)