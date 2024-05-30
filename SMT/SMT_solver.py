from SMT.SMT_utils import *

def solve_z3(model,params:dict,arrays,successor,num_c):
    from z3 import Solver,parse_smt2_string,sat
    pars=params.copy()
    if 'timeout' in params:
        pars['timeout']=int(pars['timeout']*1000)

    # print(pars['timeout'])

    try:
        solver = Solver()
        solver.set(**pars,random_seed=42)
        solver.add(parse_smt2_string(model))
    except: 
        from utils.utils import saveModel
        saveModel(model,'error','',f'SMT/models/error/')
        solver.add(parse_smt2_string(model))

    
    result = solver.check()
    
    if result == sat:
        model=solver.model()
        # get_variables(model,True,arrays=arrays,successor=successor)
        return 'sat',model,get_distances(model,False,arrays=arrays,num_c=num_c,print_=False)
    else:
        # print("UNSAT")
        
        return 'unsat',None,-1
    
def solve_cvc4(model,params):
    raise ImportError('non so come cazz installare cvc4 diavolo lupo')
    import pycvc4
    from pycvc4 import kinds

    pars=params.copy()
    if 'timeout' in params:
        pars['timeout']=int(pars['timeout']*1000)
    solver = pycvc4.Solver()
    solver.setOption("timeout", pycvc4.Term(solver, kinds.STRING, str(pars['timeout'])))
    solver.readSMTLIB2String(model)
    result = solver.checkSat()
    if result.isSat():
        print("Model:")
        model = solver.getModel()
        
        # Iterate over the model to get variable assignments
        for decl in model.getDeclarations():
            if decl.getKind() == kinds.CONST_VARIABLE:
                var_name = decl.toString()
                var_value = model.getValue(decl).toString()
                print(f"{var_name} = {var_value}")

    if result.isSat():
        return 'sat',None#TODO parse solution
    else:
        # print("UNSAT")
        return 'unsat',None

