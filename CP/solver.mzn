include "alldifferent.mzn";

% input of the problem

% number of couriers
int: num_couriers;
% number of items
int: num_items;

% couriers load size 
set of int: COURIERS = 1..m;
array[COURIERS] of int: courier_sizes;

% items size 
set of int: ITEMS = 1..n;
array[ITEMS] of int: item_sizes;

% distances
set of int: NODES = 1..n + 1;
array[NODES, NODES] of int: distances;
