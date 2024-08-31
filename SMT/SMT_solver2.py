from SMT.SMT_utils import *

def solve_z3(model,params:dict,arrays,num_c):
    from z3 import Solver,parse_smt2_string,sat
    pars=params.copy()
    if 'timeout' in params:
        pars['timeout']=int(pars['timeout']*1000)
    # to make this compatible with cvc5 we have to remove some useful keys for ccv5
    pars.pop('best',None)
    pars.pop('use_arrays',None)
    # print(pars['timeout'])

    try:
        solver = Solver()
        solver.set(**pars,  	                            )
        solver.add(parse_smt2_string(model))
    except: 
        from utils.utils import saveModel
        saveModel(model,'error','',f'SMT/models/error/')
        solver.add(parse_smt2_string(model))

    
    result = solver.check()
    
    if result == sat:
        model=solver.model()
        # get_variables(model,False,arrays=arrays,successor=successor,best=best)
        return 'sat',model,get_distances(model,lib='z3',print_names=False,arrays=arrays,num_c=num_c,print_=False)
    else:
        # print("UNSAT")
        
        return 'unsat',None,-1
    
def solve_cvc5(model, params: dict, arrays, num_c, time_queue, sat_queue, model_queue, return_queue, stop_event, best):
    import cvc5
    from cvc5 import Solver
    from queue import Queue, Empty, Full

    while not stop_event.is_set():
        tm = cvc5.TermManager()
        solver = Solver(tm)

        solver.setOption("produce-models", "true")
        
        model = model_queue.get()
        
        parser = cvc5.InputParser(solver)
        parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, model, "model")
        sm = parser.getSymbolManager()

        while True:
            cmd = parser.nextCommand()
            if cmd.isNull():
                break
            cmd.invoke(solver, sm)

        remaining_time = time_queue.get()

        try:
            sat_queue.put('sat' if solver.checkSat().isSat() else 'unsat', timeout=remaining_time)
        except Full:
            print('Timeout')
            sat_queue.put('unsat')

        vars = sm.getDeclaredTerms()

        v = (solver, vars)
        distances = get_distances(v, lib='cvc5', print_names=False, arrays=arrays, best=best, num_c=num_c, print_=False)
        solution = parse_solution(v, arrays, 'cvc5', best=best)
        return_queue.put(('sat', solution, distances))

        if stop_event.is_set():
            return_queue.put(('unsat', [], -1))
            break
