import os,sys
from utils.utils import *
from datetime import timedelta
from argparse import ArgumentParser
this_dir = os.path.dirname(os.path.abspath(__file__))
os.chdir(this_dir)

class Configuration:
    def __init__(self) -> None:
        self.instances_folder='instances_dzn'
        self.instances_names=self.read_instances()
        self.smt_models_folder='SMT/models'
        self.results_folder='test'
        self.indent_results=True
        self.first=1
        self.last=1
        self.timeout=300
        self.run_checker=False

    def read_instances(self):
        return [self.instances_folder+'/'+instance for instance in sorted(os.listdir(self.instances_folder)) if instance.endswith('.dzn')]

def load_config(config_path, configuration:Configuration):
    from check_solution import read_json_file
    config = read_json_file(config_path)
    try:
        configuration.instances_folder=config['instances_folder']
        configuration.instances_names=configuration.read_instances()
        configuration.smt_models_folder=config['smt_models_folder']
        configuration.results_folder=config['results_folder']
        configuration.indent_results=config['indent_results']
        configuration.first=config['first']
        configuration.last=config['last']
        configuration.timeout=config['timeout']
        configuration.run_checker=config['run_checker']
    except KeyError:
        raise KeyError('Invalid configuration file. It must contain:\n- instances_folder\n- smt_models_folder\n- results_folder\n- indent_results\n- first\n- last\n- timeout\n- run_checker')


def main(args):
    configuration=Configuration()
    RUN_CP=RUN_SAT=RUN_SMT=RUN_MIP=True
    if args.config:
        load_config(args.config,configuration)
    if args.instance:
        i=args.instance
        if i<1 or 1>21:raise ValueError(f'Invalid instance number. It must be in [1,21], instead got {i}')
        configuration.first=configuration.last=i
    if args.approach:
        match args.approach:
            case 'cp':
                RUN_CP=True
                RUN_SAT=RUN_SMT=RUN_MIP=False
            case 'sat':
                RUN_SAT=True
                RUN_CP=RUN_SMT=RUN_MIP=False
            case 'smt':
                RUN_SMT=True
                RUN_CP=RUN_SAT=RUN_MIP=False
            case 'mip':
                RUN_MIP=True
                RUN_CP=RUN_SAT=RUN_SMT=False
            case _:
                raise ValueError("Invalid approach. Solver must be one of: cp, sat, smt, mip")

    # ============
    # |    CP    |
    # ============
    if RUN_CP:
        import CP.CP_launcher as CP
        CP_models = {
            'model_chuffed.mzn': {
                'solvers': {
                    'chuffed': [
                        ('fs', {'timeout': timedelta(seconds=configuration.timeout), 'free_search': True}),
                        ('', {'timeout': timedelta(seconds=configuration.timeout), 'free_search': False}),
                    ]
                }
            },
            'model_gecode.mzn': {
                'solvers': {
                    'gecode': [
                        ('', {'timeout': timedelta(seconds=configuration.timeout)}),
                    ]
                }
            },
            # 'model_chuffed_SB.mzn': {
            #     'solvers': {
            #         'chuffed': [
            #             ('fs', {'timeout': timedelta(seconds=configuration.timeout), 'free_search': True}),
            #             ('', {'timeout': timedelta(seconds=configuration.timeout), 'free_search': False}),
            #         ]
            #     }
            # },
            # 'model_gecode_SB.mzn': {
            #     'solvers': {
            #         'gecode': [
            #             ('', {'timeout': timedelta(seconds=configuration.timeout)}),
            #         ]
            #     }
            # },
            'model_chuffed_short.mzn': {
                'solvers': {
                    'chuffed': [
                        ('fs', {'timeout': timedelta(seconds=configuration.timeout), 'free_search': True}),
                        ('', {'timeout': timedelta(seconds=configuration.timeout), 'free_search': False}),
                    ]
                }
            },
        }
        print('Solving with CP:')
        for instance_file in configuration.instances_names[configuration.first-1:configuration.last]:
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
            # saveJSON(instance_results,instance_file,configuration.results_folder+'/CP/',format=configuration.indent_results)
                        updateJSON(instance_results,instance_file,configuration.results_folder+'/CP_test/',format=configuration.indent_results)

    # ============
    # |    SAT   |
    # ============
    if RUN_SAT:
        import SAT.SAT_launcher as SAT

        SAT_models = {
            'circuit':[
                ('ILU', {
                    'params_name':'ILU_SB',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : True
                    }
                }),
                ('ILU', {
                    'params_name':'ILU',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : False
                    }
                }),
                ('LU', {
                    'params_name':'LU_SB',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{'symmetry':True}
                }),
                ('LU', {
                    'params_name':'LU',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{'symmetry':False}
                }),
                ('BS', {
                    'params_name':'BS2_SB',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{
                        'binary_cut' : 2,
                        'symmetry' : True
                    }
                }),
                ('BS', {
                    'params_name':'BS2',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{
                        'binary_cut' : 2,
                        'symmetry' : False
                    }
                }),
                # ('BS', {
                #     'params_name':'BS10_SB',
                #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                #     'model_params':{
                #         'binary_cut' : 10,
                #         'symmetry' : True
                #     }
                # }),
                # ('BS', {
                #     'params_name':'BS10',
                #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                #     'model_params':{
                #         'binary_cut' : 10,
                #         'symmetry' : False
                #     }
                # }),
            ],
            '1-hot-cube':[
                ('ILU', {
                    'params_name':'ILU_SB',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : True
                    }
                }),
                ('ILU', {
                    'params_name':'ILU',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{
                        'incremental_factor' : 30, 
                        'symmetry' : False
                    }
                }),
                ('LU', {
                    'params_name':'LU_SB',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{'symmetry':True}
                }),
                ('LU', {
                    'params_name':'LU',
                    'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    'model_params':{'symmetry':False}
                }),
                # comment below
                # ('BS', {
                #     'params_name':'BS2_SB',
                #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                #     'model_params':{
                #         'binary_cut' : 2,
                #         'symmetry' : True
                #     }
                # }),
                # ('BS', {
                #     'params_name':'BS2',
                #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                #     'model_params':{
                #         'binary_cut' : 2,
                #         'symmetry' : False
                #     }
                # }),
            ],
            # 'binary-cube':[
            #     ('ILU', {
            #         'params_name':'ILU_SB',
            #         'params':{'timeout': timedelta(seconds=configuration.timeout)},
            #         'model_params':{
            #             'incremental_factor' : 30, 
            #             'symmetry' : True
            #         }
            #     }),
            #     ('ILU', {
            #         'params_name':'ILU',
            #         'params':{'timeout': timedelta(seconds=configuration.timeout)},
            #         'model_params':{
            #             'incremental_factor' : 30, 
            #             'symmetry' : False
            #         }
            #     }),
                # comment below
                # ('LU', {
                #     'params_name':'LU_SB',
                #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                #     'model_params':{'symmetry':True}
                # }),
                # ('LU', {
                #     'params_name':'LU',
                #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                #     'model_params':{'symmetry':False}
                # }),
                # ('BS', {
                #     'params_name':'BS2_SB',
                #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                #     'model_params':{
                #         'binary_cut' : 2,
                #         'symmetry' : True
                #     }
                # }),
                # ('BS', {
                #     'params_name':'BS2',
                #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                #     'model_params':{
                #         'binary_cut' : 2,
                #         'symmetry' : False
                #     }
                # }),
            # ],s
        }
        
        print('Solving with SAT:')
        for instance_file in configuration.instances_names[configuration.first-1:configuration.last]:
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
                    updateJSON(instance_results,instance_file,configuration.results_folder+'/SAT/',format=configuration.indent_results)

    # ============
    # |    SMT   |
    # ============
    if RUN_SMT:
        import SMT.SMT_launcher as SMT

        SMT_models = {
                    'z3': [
                        # ('arrays_SB', {
                        #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                        #     'model_params':{
                        #         'simmetry_method':'>',
                        #         'use_arrays':True,
                        #         }
                        #     }),
                        # ('SB', {
                        #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                        #     'model_params':{
                        #         'simmetry_method':'>',
                        #         'use_arrays':False,
                        #         }
                        #     }),
                        # ('arrays', {
                        #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                        #     'model_params':{
                        #         'simmetry_method':'None',
                        #         'use_arrays':True,
                        #         }
                        #     }),
                        # ('default', {
                        #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                        #     'model_params':{
                        #         'simmetry_method':'None',
                        #         'use_arrays':False,
                        #         }
                        #     }),
                        ('best', {
                            'params':{'timeout': timedelta(seconds=configuration.timeout)},
                            'model_params':{
                                'simmetry_method':'>',
                                'best':True
                                }
                            }),
                        # ('OPT', {
                        #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                        #     'model_params':{
                        #         'z3':True
                        #         }
                        #     }),
                    ],
        }
        
        print('Solving with SMT:')
        for instance_file in configuration.instances_names[configuration.first-1:configuration.last]:
            print(f'  Solving {instance_file}...')
            instance_results={}
            for solver in SMT_models:
                for param_name,params in SMT_models[solver].copy():
                    print(f'\tUsing {solver}-{param_name}...')
                    result,model=SMT.solve_instance(instance_file,
                                        solver,
                                        params['params'],
                                        params['model_params'],
                                        verbose=False)
                    instance_results[f'{solver}_{param_name}'] = result
                    if model:saveModel(model,solver,instance_file,f'SMT/models/{solver}/{param_name}/')
                    updateJSON(instance_results,instance_file,configuration.results_folder+'/SMT/',format=configuration.indent_results)
    
    # ============
    # |    MIP   |
    # ============
    if RUN_MIP:
        import MIP.MIP_launcher as MIP
        MIP_models = {
                'solvers': {
                    'cbc': [
                        ('SB', {
                            'params':{'timeout': timedelta(seconds=configuration.timeout)},
                            'model_params':None
                            }),
                        # ('default', {
                        #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                        #     'model_params':None
                        #     }),
                    ],
                    # 'glpk': [
                    #     ('SB', {
                    #         'params':{'timeout': timedelta(seconds=configuration.timeout)},
                    #         'model_params':None
                    #         }),
                        # ('default', {
                        #     'params':{'timeout': timedelta(seconds=configuration.timeout)},
                        #     'model_params':None
                        #     }),
                    # ],
                }
            }
        print('Solving with MIP:')
        for instance_file in configuration.instances_names[configuration.first-1:configuration.last]:
            print(f'  Solving {instance_file}...')
            instance_results={}
            for solver in MIP_models['solvers']:
                for param_name,params in MIP_models['solvers'][solver].copy():
                    print(f'\tUsing {solver}-{param_name}...')
                    result,model=MIP.solve_instance(instance_file,
                                        solver,
                                        params['params'],
                                        params['model_params'],
                                        verbose=False)
                    instance_results[f'{solver}_{param_name}'] = result
                    updateJSON(instance_results,instance_file,configuration.results_folder+'/MIP/',format=configuration.indent_results)

    if configuration.run_checker:run_checker("res")

if __name__=='__main__':
    parser=ArgumentParser()
    parser.add_argument('-i',dest='instance',type=int,required=False,help='Instance number to execute. Must be in [1,21]')
    parser.add_argument('-a',dest='approach',type=str,required=False,help='What approach to use. Must be one of: cp, sat, smt, mip')
    parser.add_argument('-c',dest='config',type=str,required=False,help='JSON configuration file')
    main(parser.parse_args())