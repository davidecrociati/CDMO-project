import os
from datetime import timedelta
import CP.CP_launcher as CP
# import CP.CP_launcher_bash as CP_bash
import SAT.SAT_launcher as SAT
import MIP.MIP_launcher as MIP
import SMT.SMT_launcher as MST

from utils import *
# deve eseguire cp_launcher.launch_CP con gli adeguati parametri
# e poi potenzialmente prendere tutti i risultati e salvarli su re/CP/ ????
# etc

this_dir = os.path.dirname(os.path.abspath(__file__))
os.chdir(this_dir)
INSTANCES_FOLDER='instances_dzn' #da potenizalmente cambiare 
INSTANCES=[INSTANCES_FOLDER+'/'+instance for instance in os.listdir(INSTANCES_FOLDER) if instance.endswith('.dzn')]

RESULTS_FOLDER='res'



if __name__=='__main__':
    # ============
    # |    CP    |
    # ============
    CP_models={
        'model_drunky_ricominciamo.mzn': 'symmetry',
        
        # 'model.mzn': 'old'
        }
    CP_solvers=[
        'chuffed',
        'gecode'
        ]
    CP_params={'timeout':timedelta(seconds=300)}

    CP_JSON=[] # lista di dizionari. Ogni diz ha 'metodo':{result}
    for model,name in CP_models.items():
        for solver in CP_solvers:
            print(f'Solving CP:{name}-{solver}...')
            CP_results=CP.launch(INSTANCES[:10],model,solver,CP_params,verbose=False)
            CP_JSON=add_solutions(CP_results,name,solver,CP_JSON)

    # print(CP_JSON)
    saveJSON(CP_JSON,RESULTS_FOLDER+'/CP/',format=True)

    # ============
    # |    SAT   |
    # ============

