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
lastInstance=10 # inclusive

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
    RUN_SAT=False
    RUN_SMT=True
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
            'model_chuffed.mzn': {
                'solvers': {
                    'chuffed': [
                        ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
                        ('', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
                    ]
                }
            },
            'model_gecode.mzn': {
                'solvers': {
                    'gecode': [
                        ('', {'timeout': timedelta(seconds=TIMEOUT)}),
                    ]
                }
            },
            'model_chuffed_SB.mzn': {
                'solvers': {
                    'chuffed': [
                        ('fs', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': True}),
                        ('', {'timeout': timedelta(seconds=TIMEOUT), 'free_search': False}),
                    ]
                }
            },
            'model_gecode_SB.mzn': {
                'solvers': {
                    'gecode': [
                        ('', {'timeout': timedelta(seconds=TIMEOUT)}),
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
                        key=f'{os.path.splitext(model)[0]}_{solver}_{param_name}'
                        instance_results[key]=CP.solve_instance(instance_file,
                                                                model,
                                                                solver,
                                                                params)
            # saveJSON(instance_results,instance_file,RESULTS_FOLDER+'/CP/',format=INDENT_RESULTS)
                        updateJSON(instance_results,instance_file,RESULTS_FOLDER+'/test/',format=INDENT_RESULTS)

    # ============
    # |    SAT   |
    # ============
    if RUN_SAT:
        import SAT.SAT_launcher as SAT

        SAT_models = {
            'circuit':[
                ('ILU', {
                    'params_name':'ILU_SB',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : True
                    }
                }),
                ('ILU', {
                    'params_name':'ILU',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : False
                    }
                }),
                ('LU', {
                    'params_name':'LU_SB',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{'symmetry':True}
                }),
                ('LU', {
                    'params_name':'LU',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{'symmetry':False}
                }),
                ('BS', {
                    'params_name':'BS_SB',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'binary_cut' : 2,
                        'symmetry' : True
                    }
                }),
                ('BS', {
                    'params_name':'BS',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'binary_cut' : 2,
                        'symmetry' : False
                    }
                }),
            ],
            '1-hot-cube':[
                ('ILU', {
                    'params_name':'ILU_SB',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : True
                    }
                }),
                ('ILU', {
                    'params_name':'ILU',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : False
                    }
                }),
                ('LU', {
                    'params_name':'LU_SB',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{'symmetry':True}
                }),
                ('LU', {
                    'params_name':'LU',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{'symmetry':False}
                }),
                # comment below
                ('BS', {
                    'params_name':'BS_SB',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'binary_cut' : 2,
                        'symmetry' : True
                    }
                }),
                ('BS', {
                    'params_name':'BS',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'binary_cut' : 2,
                        'symmetry' : False
                    }
                }),
            ],
            'binary-cube':[
                ('ILU', {
                    'params_name':'ILU_SB',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : True
                    }
                }),
                ('ILU', {
                    'params_name':'ILU',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : False
                    }
                }),
                # comment below
                ('LU', {
                    'params_name':'LU_SB',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{'symmetry':True}
                }),
                ('LU', {
                    'params_name':'LU',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{'symmetry':False}
                }),
                ('BS', {
                    'params_name':'BS_SB',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'binary_cut' : 2,
                        'symmetry' : True
                    }
                }),
                ('BS', {
                    'params_name':'BS',
                    'params':{'timeout': timedelta(seconds=TIMEOUT)},
                    'model_params':{
                        'binary_cut' : 2,
                        'symmetry' : False
                    }
                }),
            ],
        }
        
        print('Solving with SAT:')
        for instance_file in INSTANCES[first-1:last]:
            print(f'  Solving {instance_file}...')
            instance_results={}
            for model in SAT_models :
                for search_name, params in SAT_models[model] :
                    print(f'\tUsing {model}-{params["params_name"]}...')
                    result=SAT.solve_instance(instance_file,
                                              model,
                                              search_name,
                                              params['params'],
                                              params['model_params'],
                                              verbose_search=False, 
                                              verbose_solver=False
                                            )
                    instance_results[f'{model}_{params["params_name"]}'] = result
                    updateJSON(instance_results,instance_file,RESULTS_FOLDER+'/SAT_test/',format=INDENT_RESULTS)

    # ============
    # |    SMT   |
    # ============
    if RUN_SMT:
        import SMT.SMT_launcher as SMT
        import SMT_2.SMT_launcher as SMT2

        SMT_models = {
                    'z3': [
                        # ('arrays_SB', {
                        #     'params':{'timeout': timedelta(seconds=TIMEOUT)},
                        #     'model_params':{
                        #         'simmetry_method':'>',
                        #         'use_arrays':True,
                        #         }
                        #     }),
                        # ('SB', {
                        #     'params':{'timeout': timedelta(seconds=TIMEOUT)},
                        #     'model_params':{
                        #         'simmetry_method':'>',
                        #         'use_arrays':False,
                        #         }
                        #     }),
                        # ('arrays', {
                        #     'params':{'timeout': timedelta(seconds=TIMEOUT)},
                        #     'model_params':{
                        #         'simmetry_method':'None',
                        #         'use_arrays':True,
                        #         }
                        #     }),
                        # ('default', {
                        #     'params':{'timeout': timedelta(seconds=TIMEOUT)},
                        #     'model_params':{
                        #         'simmetry_method':'None',
                        #         'use_arrays':False,
                        #         }
                        #     }),
                        ('best', {
                            'params':{'timeout': timedelta(seconds=TIMEOUT)},
                            'model_params':{
                                'simmetry_method':'>',
                                'best':True
                                }
                            }),
                        # ('OPT', {
                        #     'params':{'timeout': timedelta(seconds=TIMEOUT)},
                        #     'model_params':{
                        #         'z3':True
                        #         }
                        #     }),
                    ],
        }
        
        print('Solving with SMT:')
        for instance_file in INSTANCES[first-1:last]:
            print(f'  Solving {instance_file}...')
            instance_results={}
            for solver in SMT_models:
                for param_name,params in SMT_models[solver].copy():
                    print(f'\tUsing {solver}-{param_name}...')
                    result,model=SMT.solve_instance(instance_file,
                                        solver,
                                        params['params'],
                                        params['model_params'],
                                        verbose=True)
                    # print(result)
                    instance_results[f'{solver}_{param_name}'] = result
                    if model:saveModel(model,solver,instance_file,f'SMT/models/{solver}/{param_name}/')
                    updateJSON(instance_results,instance_file,RESULTS_FOLDER+'/SMT_test/',format=INDENT_RESULTS)
    
    if RUN_MIP:
        import MIP.MIP_launcher as MIP


if __name__=='__main__':
    main(sys.argv)
    if CHECKER:run_checker(firstInstance,lastInstance)