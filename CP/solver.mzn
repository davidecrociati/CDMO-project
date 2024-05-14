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

int:lower_bound;
int:upper_bound;
set of int: DISTANCE=lower_bound..upper_bound;

% items delivered by each courier
array[COURIERS, 1..num_items+2] of var NODES: stops;

% constraints for the decision variable 

% all items get delivered once 
constraint forall(i in ITEMS)(
  count(stops,i,1)
);

% couriers have to start and end in default_val
constraint forall(i in COURIERS)(
    stops[i,1]=default_val/\stops[i,num_items+2]=default_val
);

% SIMMETRIES
% to avoid permutations we must ensure that there are no adjacent 'default_val' except 
% if they go until the end of the row
constraint forall(i in COURIERS)(
  forall(j in NODES)(
    if stops[i,j]==stops[i,j+1] /\ stops[i,j]==default_val then
      count(slice_1d(row(stops,i),[j+2..num_items+2],1..num_items+1-j),default_val,num_items+1-j)
    else true
    endif
  )
);

% capacity constraint
constraint forall(i in COURIERS)(
    sum(j in ITEMS where stops[i, j+1] != default_val)(item_sizes[stops[i,j+1]]) <= courier_sizes[i]
);

array[COURIERS] of var DISTANCE:distances_traveled;

% Compute total distance
constraint forall(c in COURIERS)(
  distances_traveled[c] = sum(j in NODES)(distances[stops[c,j], stops[c,j+1]])
);
% minimize the optimization variable
var DISTANCE:longest_trip;
constraint longest_trip= max(distances_traveled);
solve :: seq_search([
  int_search(stops,first_fail, indomain_min),
  int_search(distances_traveled,first_fail, indomain_min)
  ])
  minimize(longest_trip);


output ["Stops:\n"] ++
       [ show(stops[i,j])++ ", " ++ 
         if j == num_items+2 then "\n" else "" endif |
         i in COURIERS, j in 1..num_items+2 ];

output["\nDistances travelled:\n"]++
      [ " Courier "++show(i)++": "++show(distances_traveled[i])++"\n"
      | i in COURIERS];
