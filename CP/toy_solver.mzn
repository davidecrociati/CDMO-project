% include "alldifferent.mzn";

% input of the problem

% number of couriers
int: num_couriers;
% number of items
int: num_items;

% couriers load size 
set of int: COURIERS = 1..num_couriers;
array[COURIERS] of int: courier_sizes;

% items size 
set of int: ITEMS = 1..num_items;
array[ITEMS] of int: item_sizes;

% distances
set of int: NODES = 1..num_items + 1;
array[NODES, NODES] of int: distances;

% Lettura delle variabili da un file .dzn
% include "input_data.dzn";

% Stampa delle variabili
output ["num_couriers: ", show(num_couriers), "\n"];
output ["num_items: ", show(num_items), "\n"];
output ["courier_sizes: ", show(courier_sizes), "\n"];
output ["item_sizes: ", show(item_sizes), "\n"];
output ["distances: ", show(distances[3,4]), "\n"]; 