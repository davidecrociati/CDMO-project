def parse_dzn(filename):
    data = {}
    with open(filename, 'r') as file:
        content = file.read()
        content = content.replace('\n', '')
        assignments = content.split(';')
        
        for assignment in assignments:
            if '=' in assignment:
                key, value = assignment.split('=')
                key = key.strip()
                value = value.strip()
                
                if value.startswith('[') and value.endswith(']'):
                    if '|'.join(value).count('|') > 0:
                        # Handle 2D array
                        value = value[1:-1].strip().split('|')
                        array_2d = []
                        for row in value:
                            if row:
                                array_2d.append([int(v.strip()) for v in row.split(',')])
                        data[key] = array_2d
                    else:
                        # Handle 1D array
                        value = value[1:-1].split(',')
                        data[key] = [int(v.strip()) for v in value]
                else:
                    data[key] = int(value)
    return data