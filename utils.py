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