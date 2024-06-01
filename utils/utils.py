import os
import json
import check_solution as check


def add_solutions(solutions,name,solver,outputList):
    for i,solution in enumerate(solutions):
        if len(outputList)==i:
            new_entry={f'{name}_{solver}':solution}
            outputList.append(new_entry)
        else:
            outputList[i][f'{name}_{solver}']=solution

    return outputList


def saveJSON(content:dict,dzn_path,folder,format=False):
    os.makedirs(folder, exist_ok=True)
    filename = folder+'/'+os.path.splitext(os.path.basename(dzn_path))[0]+'.json'
    with open(filename, 'w') as file:
        indent= None if not format else 4
        json.dump(content, file, indent=indent)

def updateJSON(content:dict,dzn_path,folder,format=False):
    # logic to preserve the order of the dict and remove ending '_'
    new_content = {}
    for key, value in content.items():
        if key.endswith('_'):
            new_content[key[:-1]] = value
        else:
            new_content[key] = value
    content.clear()
    content.update(new_content)
    os.makedirs(folder, exist_ok=True)
    filename = folder+'/'+os.path.splitext(os.path.basename(dzn_path))[0]+'.json'
    with open(filename, 'w') as file:
        indent= None if not format else 4
        json.dump(content, file, indent=indent)

def saveModel(content,solver,inst_name,folder):
    if not os.path.exists(folder):
        os.makedirs(folder)

    filename=folder+f'{solver}_'+os.path.splitext(os.path.basename(inst_name))[0]+'.smt2'
    with open(filename,'w') as file:
        file.write(content)

def saveJSON_list(JSONList,folder,format=False,firstInstanceNumber=1):
    # script_dir = os.path.dirname(os.path.abspath(__file__))
    # os.chdir(script_dir)
    os.makedirs(folder, exist_ok=True)
    for instance, results in enumerate(JSONList, start=firstInstanceNumber):
        filename = os.path.join(folder, f"{instance:02}.json")
        with open(filename, 'w') as file:
            indent= None if not format else 4
            json.dump(results, file, indent=indent)


def getNumber(instance_path):
    # print(instance_path,instance_path[-6:-4])
    return int(instance_path[-6:-4])


def run_checker(first,last):
    check.main(['','./instances/', './res/', first, last])


def parse_dzn(dzn_path):
    data = {}
    with open(dzn_path, 'r') as file:
        content = file.read()
        content = content.replace('\n', '')
        values = content.split(';')
        
        for value in values:
            if '=' in value:
                key, value = value.split('=')
                key = key.strip()
                value = value.strip()
                
                if value.startswith('[') and value.endswith(']'):
                    if '|'.join(value).count('|') > 0:
                        # Handle 2D array
                        value = value[1:-1].strip().split('|')
                        array_2d = []
                        if len(value)>1:
                            for row in value:
                                if row:
                                    array_2d.append([int(v.strip()) for v in row.split(',')])
                            data[key] = array_2d
                        else:
                            # Handle 1D array
                            value = value[0].split(',')
                            data[key] = [int(v.strip()) for v in value]
                else:
                    data[key] = int(value)
    return data