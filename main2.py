import os
from datetime import timedelta
import CP.CP_launcher as CP
import SAT.SAT_launcher as SAT
import MIP.MIP_launcher as MIP
import SMT.SMT_launcher as SMT
from utils.utils import *

this_dir = os.path.dirname(os.path.abspath(__file__))
os.chdir(this_dir)
INSTANCES_FOLDER='instances_dzn' #da potenizalmente cambiare 
INSTANCES=[INSTANCES_FOLDER+'/'+instance for instance in sorted(os.listdir(INSTANCES_FOLDER)) if instance.endswith('.dzn')]

SMT_MODELS_FOLDER='SMT/models'

RESULTS_FOLDER='res'
INDENT_RESULTS=True # indented results on the json

firstInstance=1 # inclusive
lastInstance=21 # inclusive

if firstInstance<0:
    firstInstance=1
if lastInstance>21:
    lastInstance=21

TIMEOUT=300 # seconds

RUN_CP=True
RUN_SAT=False
RUN_SMT=False
RUN_MIP=False

CHECKER=False


def main():
    # ============
    # |    CP    |
    # ============
    CP_models = {
        'model_gecode.mzn': {
            'solvers': {
                'gecode': [
                    ('no_fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
                    ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
                ]
            }
        },
        'model_chuffed.mzn': {
            'solvers': {
                'chuffed': [
                    ('no_fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
                    ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
                ]
            }
        },
        # 'model_gecode_copy.mzn': {
        #     'solvers': {
        #         'gecode': [
        #             ('no_fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
        #             ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
        #         ]
        #     }
        # },
        # 'model_chuffed_copy.mzn': {
        #     'solvers': {
        #         'chuffed': [
        #             ('no_fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
        #             ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
        #         ]
        #     }
        # }
    }

    if RUN_CP:
        for instance_file in INSTANCES[firstInstance-1:lastInstance]:
            print(f'Solving {instance_file}...')
            instance_results={}
            for model in CP_models:
                # print(model)
                for solver in CP_models[model]['solvers']:
                    # print(solver)
                    for param_name,params in CP_models[model]['solvers'][solver]:
                        print(f'\tUsing {model} with {solver}-{param_name}...')
                        instance_results[
                            f'{os.path.splitext(model)[0]}_{solver}_{param_name}'
                        ]=CP.solve_instance(instance_file,
                                            model,
                                            solver,
                                            params)
            saveJSON(instance_results,instance_file,RESULTS_FOLDER+'/CP2/',format=INDENT_RESULTS)



    # if RUN_CP:
    #     CP_JSON=[] # lista di dizionari. Ogni diz ha 'metodo':{result}
    #     for model,name in CP_models.items():
    #         for solver in CP_solvers:
    #             print(f'Solving CP: {name}-{solver}...')
    #             CP_results=CP.launch(INSTANCES[firstInstance-1:lastInstance],model,solver,CP_params,verbose=False)
    #             CP_JSON=add_solutions(CP_results,name,solver,CP_JSON)

    #     # print(CP_JSON)
    #     saveJSON_list(CP_JSON,RESULTS_FOLDER+'/CP/',format=True,firstInstanceNumber=firstInstance)

    # ============
    # |    SAT   |
    # ============
    SAT_models={
        'placeholder': 'sat_test',
        
        # 'model.mzn': 'old'
        }
    SAT_solvers=[
        'blank',
        # 'gecode'
        ]
    SAT_params={
        'timeout':timedelta(seconds=300),
        } # those are default


    if RUN_SAT:
        SAT_JSON=[] # lista di dizionari. Ogni diz ha 'metodo':{result}
        for model,name in SAT_models.items():
            for solver in SAT_solvers:
                print(f'Solving SAT: {name}-{solver}...')
                SAT_results=SAT.launch(INSTANCES[firstInstance-1:lastInstance],SAT_params,verbose=False)
                SAT_JSON=add_solutions(SAT_results,name,solver,SAT_JSON)

        # print(SAT_JSON)
        saveJSON_list(SAT_JSON,RESULTS_FOLDER+'/SAT/',format=True,firstInstanceNumber=firstInstance)

    # ============
    # |    SMT   |
    # ============
    SMT_models={
        'placeholder': 'smt_test',
        
        # 'model.mzn': 'old'
        }
    SMT_solvers=[
        'blank',
        # 'gecode'
        ]
    SMT_params = {
            'timeout': 300_000, # microseconds
        }  # those are default

    if RUN_SMT:
        models=SMT.generate_smt2_models(INSTANCES[firstInstance-1:lastInstance],SMT_MODELS_FOLDER)

    if RUN_SMT:
        SMT_JSON=[] # lista di dizionari. Ogni diz ha 'metodo':{result}
        for model,name in SMT_models.items():
            for solver in SMT_solvers:
                print(f'Solving SMT: {name}-{solver}...')
                SMT_results=SMT.launch(models,SMT_params,verbose=False)
                SMT_JSON=add_solutions(SMT_results,name,solver,SMT_JSON)

        # print(SMT_JSON)
        saveJSON_list(SMT_JSON,RESULTS_FOLDER+'/SMT/',format=True,firstInstanceNumber=firstInstance)

if __name__=='__main__':
    main()
    if CHECKER:run_checker(firstInstance,lastInstance)