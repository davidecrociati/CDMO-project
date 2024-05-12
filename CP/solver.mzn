include "globals.mzn";

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

% items delivered by each courier
array[COURIERS,ITEMS] of var 0..num_items: delivers;

% constraints for the decision variable delivers

% constraint per il peso
constraint forall(c in COURIERS)(
    % prendo gli indici degli elementi diversi da zero per ogni corriere,
    % poi itero su quegli indici e controllo che la somma sia minore di itemsize
    sum(j in ITEMS where delivers[c, j] != 0)(item_sizes[j]) <= courier_sizes[c]
);

% constraint un corriere consegni solo una volta un certo item
constraint forall(i in COURIERS)(
  all_different_except_0(delivers[i,ITEMS])::domain
);

% constraint un item può essere consegnato solo da un corriere
constraint forall(j in ITEMS) (
    count([delivers[i, j]|i in COURIERS],0,num_couriers-1)
);

% constraint che tutti i pacchi sono presi in carico
constraint forall(j in ITEMS) (
    sum(i in COURIERS)(delivers[i, j]) >= 1
);

% define the optimization variable
array[COURIERS] of var int:distances_traveled;

% minimize the optimization variable
var int:longest_trip = max(distances_traveled)
solve minimize longest_trip;

output ["Delivers:\n"] ++
       [ show(delivers[i,j]) ++ ", " ++ 
         if j == num_items then "\n" else "" endif |
         i in COURIERS, j in ITEMS ];

output["\nDistances travelled:\n"]++
      [ " Courier "++show(i)++": "++show(distances_traveled[i])++"\n"
      | i in COURIERS];