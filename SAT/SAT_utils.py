from z3 import *


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
    print("courier_sizes:", instance['courier_sizes'])
    print("item_sizes:", instance['item_sizes'])
    print("distances:")
    for row in instance['distances']:
        print("  ", row)
    print("lower_bound:", instance['lower_bound'])
    print("upper_bound:", instance['upper_bound'])