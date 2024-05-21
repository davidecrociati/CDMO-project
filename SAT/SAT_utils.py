from z3 import *

def print_responsabilities(model, resp):
    s='Responsabilities:\nItems: '
    s+=' '.join(str(i+1) for i in range(len(resp)))+'\n'+'--'*(len(resp)+3)+'\nCour:  '
    for i in range(len(resp)):
        for c in range(len(resp[i])):
            if is_true(model[resp[i][c]]):
                s+=f'{c+1} '
                # break
        # s+='\n'
    print(s)


def display_instance(instance):
    print("num_items:", instance['num_items'])
    print("courier_sizes:", instance['courier_sizes'])
    print("item_sizes:", instance['item_sizes'])
    print("distances:")
    for row in instance['distances']:
        print("  ", row)
    print("lower_bound:", instance['lower_bound'])
    print("upper_bound:", instance['upper_bound'])