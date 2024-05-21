from datetime import timedelta
from  utils.utils import parse_dzn
import SAT.solver as solver
import time
import math


def launch(instances: list, params: dict = None, verbose=False):

    if params == None:
        params = {
            'timeout': timedelta(seconds=300),
        }  # those are default

    results = []
    for instance in instances:
        print(f'Solving {instance}...')
        execTime = time.time()
        instance_data = parse_dzn(instance)
        # TODO il solver nn prende il parametro del tempo
        solution = solver.solve(instance_data)
        execTime = math.floor(time.time()-execTime)
        if execTime > params['timeout'].total_seconds():
            execTime = params['timeout'].total_seconds()
        obj = solution[0]
        if obj == -1:
            obj = 'n/a'
        results.append({
            "time": execTime,
            "optimal": (execTime < params['timeout'].total_seconds()),
            "obj": obj,
            "sol": solution[1]
        })

    return results


# if __name__=='__main__':
#     this_dir = os.path.dirname(os.path.abspath(__file__))
#     os.chdir(this_dir)

#     file='instances_dzn/inst01.dzn'
#     file2='instances_dzn/inst02.dzn'

#     # print(parse_dzn(file))
#     print(launch([file,file2]))
