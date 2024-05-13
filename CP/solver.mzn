include "globals.mzn";

% number of couriers
int: num_couriers;
% number of items
int: num_items;

% couriers load size 
set of int: COURIERS = 1..num_couriers;
set of int: ITEMS = 1..num_items;
set of int: NODES = 1..num_items + 1;
int: default_val=num_items + 1;

% items size 
array[COURIERS] of int: courier_sizes;
array[ITEMS] of int: item_sizes;
array[NODES, NODES] of int: distances;


% items delivered by each courier
array[COURIERS, ITEMS] of var NODES: delivers;

% constraints for the decision variable delivers

% constraint per il peso
constraint forall(c in COURIERS)(
    % prendo gli indici degli elementi diversi da zero per ogni corriere,
    % poi itero su quegli indici e controllo che la somma sia minore di itemsize
    sum(j in ITEMS where delivers[c, j] != default_val)(item_sizes[j]) <= courier_sizes[c]
);

% constraint un corriere consegni solo una volta un certo item
constraint forall(i in COURIERS)(
  all_different_except(delivers[i,ITEMS],{default_val})::domain
);

% constraint un item può essere consegnato solo da un corriere
constraint forall(j in ITEMS) (
    count([delivers[i, j]|i in COURIERS],default_val,num_couriers-1)
);

% constraint che tutti i pacchi sono presi in carico
constraint forall(j in ITEMS) (
    sum(i in COURIERS)(delivers[i, j]) <num_items*default_val
);

constraint forall(i in COURIERS, j in ITEMS)(
  if delivers[i,j] != default_val then
    delivers[i,j] <= num_items - count(row(delivers, i), default_val)
  else
    true
  endif
);

% define the optimization variable
array[COURIERS, 1..num_items+2] of var NODES: aux_stops;

% couriers have to start from the starting point
constraint forall(i in COURIERS)(
  aux_stops[i,1]=default_val %/\ aux_stops[i,num_items+2]=default_val
);

constraint forall(i in COURIERS)(
  slice_1d(row(aux_stops,i),[2..num_items+1],1..num_items)=arg_sort(row(delivers,i))
);


array[COURIERS] of var int:num_items_delivered;
constraint forall(c in COURIERS)(
  num_items_delivered[c]=num_items-count(row(delivers, c), default_val)
);

array[COURIERS, 1..num_items+2] of var NODES: stops;
% i valori dei non-item devono diventare default_val
constraint forall(i in COURIERS,j in 1..num_items+2)(
  if j<=num_items_delivered[i]+1 then
    stops[i,j]=aux_stops[i,j]
    else
    stops[i,j]=default_val
    endif
);

array[COURIERS] of var int:distances_traveled;

% Compute total distance
constraint forall(c in COURIERS)(
  distances_traveled[c] = sum(j in NODES)(distances[stops[c,j], stops[c,j+1]])
);
% minimize the optimization variable
var int:longest_trip = max(distances_traveled);
solve minimize longest_trip;

output ["Delivers:\n"] ++
       [ show(delivers[i,j]) ++ ", " ++ 
         if j == num_items then "\n" else "" endif |
         i in COURIERS, j in ITEMS ];

output["\nNum items delivered:\n"]++
      [ " Courier "++show(i)++": "++show(num_items_delivered[i])++"\n"
      | i in COURIERS];

output ["Stops:\n"] ++
       [ show(stops[i,j]) ++ ", " ++ 
         if j == num_items+2 then "\n" else "" endif |
         i in COURIERS, j in 1..num_items+2 ];

output["\nDistances travelled:\n"]++
      [ " Courier "++show(i)++": "++show(distances_traveled[i])++"\n"
      | i in COURIERS];
