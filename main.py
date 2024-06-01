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


firstInstance=7 # inclusive
lastInstance=7 # inclusive

if firstInstance<=0:
    firstInstance=1
if lastInstance>21:
    lastInstance=21
if firstInstance>lastInstance:
    lastInstance=firstInstance

TIMEOUT=300 # seconds


CHECKER=False


def main(argv):
    RUN_CP=False
    RUN_SAT=True
    RUN_SMT=False
    RUN_MIP=False
    first=firstInstance
    last=lastInstance
    if len(argv)>1:
        first=last=int(argv[1])
        if len(argv)>2:
            match argv[2]:
                case 'cp':
                    RUN_CP=True
                    RUN_SAT=False
                    RUN_SMT=False
                    RUN_MIP=False
                case 'sat':
                    RUN_CP=False
                    RUN_SAT=True
                    RUN_SMT=False
                    RUN_MIP=False
                case 'smt':
                    RUN_CP=False
                    RUN_SAT=False
                    RUN_SMT=True
                    RUN_MIP=False
                case 'mip':
                    RUN_CP=False
                    RUN_SAT=False
                    RUN_SMT=False
                    RUN_MIP=True
                case _:
                    pass


    # ============
    # |    CP    |
    # ============
    if RUN_CP:
        import CP.CP_launcher as CP
        CP_models = {
            'model_gecode.mzn': {
                'solvers': {
                    'gecode': [
                        ('', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
                        # ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
                    ]
                }
            },
            'model_gecode_SB.mzn': {
                'solvers': {
                    'gecode': [
                        ('', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
                        # ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
                    ]
                }
            },
            'model_chuffed.mzn': {
                'solvers': {
                    'chuffed': [
                        ('', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
                        ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
                    ]
                }
            },
            'model_chuffed_SB.mzn': {
                'solvers': {
                    'chuffed': [
                        ('', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
                        ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
                    ]
                }
            },
        }
        print('Solving with CP:')
        for instance_file in INSTANCES[first-1:last]:
            print(f'  Solving {instance_file}...')
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

        SAT_params = {
                'timeout': timedelta(seconds=TIMEOUT),
                'search' : {
                    'binary_cut' : 2, 
                    'incremental_factor' : 30
                }
                # 'no_time_out': {},
            }
        
        SAT_models = ['1-hot-cube', 'binary-cube', 'circuit']
        
        SAT_searches = {
            "lower_upper" : "LU",
            'upper_lower' : "UL", 
            'incremental_lower_upper' : "ILU",
            'binary_search' : "BS"
        }
        
        print('Solving with SAT:')
        for n, instance_file in enumerate(INSTANCES[first-1:last], 1):#TODO QUI NON PARTE SEMPRE DA 1 FIXARE
            print(f'  Solving {instance_file}...')
            instance_results={}
            for model in SAT_models :
                for search_name, s in SAT_searches.items() :
                    result=SAT.solve_instance(instance_file,SAT_params,search_name, model, symmetry=(n > 10))
                    if (n > 10) : sym="SYM"
                    else : sym="NO_SYM"
                    instance_results[f'{model}_{s}_{sym}'] = result
            saveJSON(instance_results,instance_file,RESULTS_FOLDER+'/SAT/',format=INDENT_RESULTS)
                    
                    
        # print('Solving with SAT:')
        # for instance_file in INSTANCES[first-1:last]:
        #     print(f'Solving {instance_file}...')
        #     instance_results={}
        #     for param_name,params in SAT_params.items():
        #         print(f'\tUsing {param_name} params...')
        #         result=SAT.solve_instance(instance_file,params)
        #         # print(result)
        #         instance_results[f'{param_name}'] = result
        #     saveJSON(instance_results,instance_file,RESULTS_FOLDER+'/SAT2/',format=INDENT_RESULTS)

    # ============
    # |    SMT   |
    # ============
    if RUN_SMT:
        import SMT.SMT_launcher as SMT

        SMT_models = {
                'solvers': {
                    'z3': [
                        ('SB', {
                            'params':{'timeout': timedelta(seconds=TIMEOUT)},
                            'model_params':{
                                'simmetry_method':'>',
                                'use_successors':True,
                                'use_arrays':False,
                                }
                            }),
                        ('arrays_SB', {
                            'params':{'timeout': timedelta(seconds=TIMEOUT)},
                            'model_params':{
                                'simmetry_method':'>',
                                'use_successors':True,
                                'use_arrays':True,
                                }
                            }),
                        ('arrays', {
                            'params':{'timeout': timedelta(seconds=TIMEOUT)},
                            'model_params':{
                                'simmetry_method':'None',
                                'use_successors':True,
                                'use_arrays':False,
                                }
                            }),
                        # ('default', {
                        #     'params':{'timeout': timedelta(seconds=TIMEOUT)},
                        #     'model_params':None
                        #     }),
                    ],
                }
            }
        print('Solving with SMT:')
        for instance_file in INSTANCES[first-1:last]:
            print(f'  Solving {instance_file}...')
            instance_results={}
            for solver in SMT_models['solvers']:
                for param_name,params in SMT_models['solvers'][solver].copy():
                    print(f'\tUsing {solver}-{param_name}...')
                    result,model=SMT.solve_instance(instance_file,
                                        solver,
                                        params['params'],
                                        params['model_params'],
                                        verbose=False)
                    # print(result)
                    instance_results[f'{solver}_{param_name}'] = result
                    if model:saveModel(model,solver,instance_file,f'SMT/models/{solver}/')
            saveJSON(instance_results,instance_file,RESULTS_FOLDER+'/SMT/',format=INDENT_RESULTS)
    
    if RUN_MIP:
        import MIP.MIP_launcher as MIP


if __name__=='__main__':
    main(sys.argv)
    if CHECKER:run_checker(firstInstance,lastInstance)