
def tolist(solution):
    '''
	solution is a string [[i1,i2],[i3,i4,i5],...[]]

    output must be that string parsed to a list
    '''
    # first value is the default_value, I hope that this holds always
    solution=[list(dict.fromkeys(r))[1:] for r in solution]
    return solution