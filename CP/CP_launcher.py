from minizinc import Instance, Model, Solver
from datetime import timedelta
import os

def solve_mzn(mzn_file, dzn_file,solver,params:dict={}):
    model = Model(mzn_file)

    model.add_file(dzn_file)

    solver = Solver.lookup(solver)

    instance = Instance(solver, model)
    # TODO fargli passare i parametri (quali ?)
    result = instance.solve(timeout=timedelta(seconds=15))

    return result

def launch_CP(instances:list,model:str='model.mzn',solver:str='chuffed',params:dict={}):
    '''
    Parameters:
    instances (list): A list of file paths to the instance files to be solved.
    model (str): The file path to the MiniZinc model file.
    solver (str): The solver to use for solving the instances.
    params (dict): Additional parameters to pass to the solver.

    Returns:
    dict: A dictionary where keys are instance file paths and values are the solutions.
    '''
    script_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(script_dir)

    results={}
    for instance in instances[:]:
        print(f"Solving {instance} ...")
        
        solution = solve_mzn(model, instance,solver,params)
        stats = getattr(solution,'statistics')
        # TODO : SCEGLIERE TRA 
        execTime = stats['time'].total_seconds() 
        # • 'flatTime' --> dall'inizio alla fine dell'esecuzione del solutore, senza tener conto del tempo di inizializzazione 
        # • 'time' --> tempo totale trascorso per l'intero processo
        # • 'initTime' --> tempo impiegato per inizializzare il problema
        # • 'solveTime' --> tempo impiegato specificamente per risolvere il problema, escludendo il tempo di inizializzazione e di eventuale ottimizzazione
        # • 'optTime' --> tempo impiegato per l'ottimizzazione
        # ==> time = initTime + (flatTime) = initTime + (solveTime + optTime)
        
        results[instance]= {
            "time" : execTime,
            "optimal" : (execTime==300), # TODO : parametrizzabile ?
            "obj" : stats['objective'],
            "sol" : str(solution) # output del modello (da fare su una riga sola)
        }
        
        print(results[instance])
        
    return results

if __name__=='__main__':
    script_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(script_dir)

    instances_folder='../instances_dzn'
    # instances_folder='.'
    instances=[instances_folder+'/'+instance for instance in os.listdir(instances_folder) if instance.endswith('.dzn')]
    instances.sort()
    mzn_file = 'model.mzn'
    mzn_file = 'model_drunky.mzn'
    # mzn_file = 'working_solver.mzn'
    
    print(launch_CP(instances))

    # for instance in instances:
    #     print(f'Solving {instance[len(instances_folder)+1:]}...')
    #     solution = solve_mzn(mzn_file, instance,'chuffed')
    #     print()
    #     # print(getattr(solution,'statistics'))
