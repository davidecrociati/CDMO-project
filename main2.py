import os,sys
from datetime import timedelta
from utils.utils import *

this_dir = os.path.dirname(os.path.abspath(__file__))
os.chdir(this_dir)
INSTANCES_FOLDER='instances_dzn' #da potenzialmente cambiare 
INSTANCES=[INSTANCES_FOLDER+'/'+instance for instance in sorted(os.listdir(INSTANCES_FOLDER)) if instance.endswith('.dzn')]

SMT_MODELS_FOLDER='SMT/models'

RESULTS_FOLDER='res'
INDENT_RESULTS=True # indented results on the json


firstInstance=1 # inclusive
lastInstance=6 # inclusive

if firstInstance<=0:
    firstInstance=1
if lastInstance>21:
    lastInstance=21
if firstInstance>lastInstance:
    lastInstance=firstInstance

TIMEOUT=300 # seconds

RUN_CP=False
RUN_SAT=False
RUN_SMT=True
RUN_MIP=False

CHECKER=False


def main(argv):
    try:
        firstInstance=lastInstance=int(argv[1])
    except:pass

    # ============
    # |    CP    |
    # ============
    if RUN_CP:
        import CP.CP_launcher as CP
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

    # ============
    # |    SAT   |
    # ============
    if RUN_SAT:
        import SAT.SAT_launcher as SAT

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
    if RUN_SMT:
        import SMT.SMT_launcher as SMT

        SMT_models = {
                'solvers': {
                    'z3': [
                        ('default', {'timeout': timedelta(seconds=TIMEOUT)}),
                    ],
                    # 'cvc4':[
                    #     ('', {'timeout': timedelta(seconds=TIMEOUT)}),
                    # ]
                }
            }

        for instance_file in INSTANCES[firstInstance-1:lastInstance]:
            print(f'Solving {instance_file}...')
            instance_results={}
            for solver in SMT_models['solvers']:
                for param_name,params in SMT_models['solvers'][solver].copy():
                    print(f'\tUsing {solver}-{param_name}...')
                    result,model=SMT.solve_instance(instance_file,
                                        solver,
                                        params)
                    # print(result)
                    instance_results[f'{solver}_{param_name}'] = result
                    if model:
                        saveModel(model,solver,instance_file,f'SMT/models/{solver}/')
            saveJSON(instance_results,instance_file,RESULTS_FOLDER+'/SMT/',format=INDENT_RESULTS)
    if RUN_MIP:
        import MIP.MIP_launcher as MIP


if __name__=='__main__':
    main(sys.argv)
    if CHECKER:run_checker(firstInstance,lastInstance)