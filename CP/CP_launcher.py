import pymzn
import os

def solve_mzn(mzn_file, dzn_file):
    # Load the MiniZinc model
    types={
        "num_couriers": {"type" : "int"},
        "num_items": {"type" : "int"},
        # "COURIERS": {"type" : "int", "set" : true},
        "courier_sizes": {"type" : "int", "dim" : 1, "dims" : ["int"]},
        # "ITEMS": {"type" : "int", "set" : true},
        "item_sizes": {"type" : "int", "dim" : 1, "dims" : ["int"]},
        # "NODES": {"type" : "int", "set" : true},
        "distances": {"type" : "int", "dim" : 2, "dims" : ["int","int"]}
   }
    
    # types = {
    #     "num_couriers": 'int',
    #     "num_items": 'int',
    #     "courier_sizes": 'array[int] of int',
    #     "item_sizes": 'array[int] of int',
    #     "distances": 'array[int, int] of int'
    # }
    
    data = pymzn.dzn2dict(dzn_file,types=types)
    # print(data)
    # model = pymzn.minizinc(mzn_file)

    # Load the MiniZinc data file

    # Solve the MiniZinc model with the provided data
    result = pymzn.minizinc(mzn_file, data=data, output_mode='json')

    return result

if __name__=='__main__':

    script_dir = os.path.dirname(os.path.abspath(__file__))

    os.chdir(script_dir)
    # Example usage
    mzn_file = 'toy_solver.mzn'
    dzn_file = '../instances_dzn/inst01.dzn'
    solution = solve_mzn(mzn_file, dzn_file)
    print(solution)
