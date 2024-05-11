import os

def insert_commas(string:str):
    '''
	From a string in the form '2 3 4 3 4 4 0' returns a single string '2, 3, 4, 3, 4, 4, 0'
    '''
    elements = string.split()
    formatted_string = ", ".join(elements)
    return formatted_string


def write_new_content(data, variables):
    content = ''
    content += variables[0]+'='+data[0]+';\n'
    content += variables[1]+'='+data[1]+';\n'
    content += variables[2]+'=['+insert_commas(data[2])+'];\n'
    content += variables[3]+'=['+insert_commas(data[3])+'];\n'
    content+=variables[4]+'=['
    for table_row in data[4:]:
        content+='|'+insert_commas(table_row)+'\n'
    content=content[:-1]
    content+='|];\n'
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
    
    variables=['num_couriers','num_items','courier_sizes','item_sizes','distances']
    
    for file_name in file_names:
        if file_name.endswith(".dat"):
            file_path = os.path.join(instances_folder, file_name)

            data=read_file(file_path)
            formatted_data=write_new_content(data,variables)

            dzn_file_name=DZN_instances_folder+'/'+file_name[:-4]
            save_dzn_file(dzn_file_name,formatted_data)