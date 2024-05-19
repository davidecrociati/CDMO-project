import os
from datetime import timedelta
import CP.CP_launcher as CP
import SAT.SAT_launcher as SAT
import MIP.MIP_launcher as MIP
import SMT.SMT_launcher as MST
from utils import *

this_dir = os.path.dirname(os.path.abspath(__file__))
os.chdir(this_dir)
INSTANCES_FOLDER='instances_dzn' #da potenizalmente cambiare 
INSTANCES=[INSTANCES_FOLDER+'/'+instance for instance in os.listdir(INSTANCES_FOLDER) if instance.endswith('.dzn')]

RESULTS_FOLDER='res'



def main():
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
    CP_params={
        'timeout':timedelta(seconds=300),
        'free_search':False
        } # those are default

    RUN_CP=True
    if RUN_CP:
        CP_JSON=[] # lista di dizionari. Ogni diz ha 'metodo':{result}
        for model,name in CP_models.items():
            for solver in CP_solvers:
                print(f'Solving CP: {name}-{solver}...')
                CP_results=CP.launch(INSTANCES[:10],model,solver,CP_params,verbose=False)
                CP_JSON=add_solutions(CP_results,name,solver,CP_JSON)

        # print(CP_JSON)
        saveJSON(CP_JSON,RESULTS_FOLDER+'/CP/',format=True)

    # ============
    # |    SAT   |
    # ============
    SAT_models={
        'placeholder': 'sat_test',
        
        # 'model.mzn': 'old'
        }
    SAT_solvers=[
        'blank',
        'gecode'
        ]
    SAT_params={
        'timeout':timedelta(seconds=300),
        } # those are default

    RUN_SAT=True

    if RUN_SAT:
        SAT_JSON=[] # lista di dizionari. Ogni diz ha 'metodo':{result}
        for model,name in SAT_models.items():
            for solver in SAT_solvers:
                print(f'Solving SAT: {name}-{solver}...')
                SAT_results=SAT.launch(INSTANCES[:10],SAT_params,verbose=False)
                SAT_JSON=add_solutions(SAT_results,name,solver,SAT_JSON)

        # print(SAT_JSON)
        saveJSON(SAT_JSON,RESULTS_FOLDER+'/SAT/',format=True)

if __name__=='__main__':
    main()