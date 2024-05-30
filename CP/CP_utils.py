
def tolist(solution):
    '''
	solution is a string [[i1,i2],[i3,i4,i5],...[]]

    output must be that string parsed to a list
    '''
    depot = len(solution[0]) +1
    res = []
    for r in solution:
        r = list(dict.fromkeys(r))
        if depot in r:
            r.remove(depot)
        res.append(r)
    return res