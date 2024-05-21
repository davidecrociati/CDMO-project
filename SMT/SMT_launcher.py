import subprocess
from z3 import *
import os

def launch(file_path):
    # Parse the SMT2 file
    solver = Solver()
    solver.add(parse_smt2_file(file_path))
    
    # Check satisfiability
    result = solver.check()
    
    print(result)
    
    if result == sat:
        # If satisfiable, print the model
        print(solver.model())
    else:
        print("No model found.")
    

if __name__ == "__main__":
    # Path to the SMT2 file
    smt2_file_path = 'SMT/model.smt2'
    print(os.path.exists(smt2_file_path))
    # Run the SMT2 solver on the file
    launch(smt2_file_path)
