import sys,os
sys.path.append(os.path.dirname(os.path.dirname(__file__)))
from utils import parse_dzn


def generate_smt2_model(dzn_instance):
    instance_data=parse_dzn(dzn_instance)

    num_couriers = instance_data['num_couriers']
    num_items = instance_data['num_items']
    courier_sizes = instance_data['courier_sizes']
    item_sizes = instance_data['item_sizes']
    distances = instance_data['distances']
    lower_bound = instance_data['lower_bound']
    upper_bound = instance_data['upper_bound']

    model_content = f"""
(set-logic QF_FD)
(declare-const num_couriers Int)
(assert (= num_couriers {num_couriers}))
(declare-const num_items Int)
(assert (= num_items {num_items}))
"""
    for i, size in enumerate(courier_sizes, start=1):
        model_content += f"(declare-const courier_{i}_size Int)\n"
        model_content += f"(assert (= courier_{i}_size {size}))\n"
    for i, size in enumerate(item_sizes, start=1):
        model_content += f"(declare-const item_{i}_size Int)\n"
        model_content += f"(assert (= item_{i}_size {size}))\n"

    # TODO continue...

    model_content+='(check-sat)\n(get-model)'

    return model_content


def parse_solution(result):
    # TODO

    return -1,[]