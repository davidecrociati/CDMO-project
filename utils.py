import os
import json

def add_solutions(solutions,name,solver,outputList):
    for i,solution in enumerate(solutions):
        if len(outputList)==i:
            new_entry={f'{name}_{solver}':solution}
            outputList.append(new_entry)
        else:
            outputList[i][f'{name}_{solver}']=solution

    return outputList


def saveJSON(JSONList,folder,format=False):
    script_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(script_dir)
    os.makedirs(folder, exist_ok=True)
    for instance, results in enumerate(JSONList, start=1):
        filename = os.path.join(folder, f"{instance:02}.json")
        with open(filename, 'w') as file:
            indent= None if not format else 4
            json.dump(results, file, indent=indent)

def tolist(solution):
    '''
	solution is a string [[i1,i2],[i3,i4,i5],...[]]

    output must be that string parsed to a list
    '''
    # rows=str(solution).split('\n')
    # rows=[r.split(',')[:-1] for r in rows]
    # rows=[[int(e) for e in r]for r in rows]
    # default=rows[0][0]
    # rows=[list(dict.fromkeys(r)) for r in rows]
    # rows=[[e for e in r if e!=default] for r in rows]
    # return rows
    # default=solution[0][0]

    # first value is the default_value, I hope that this holds always
    solution=[list(dict.fromkeys(r))[1:] for r in solution]
    return solution
