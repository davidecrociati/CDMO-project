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

% items delivered by each courier
array[COURIERS, 1..num_items+2] of var NODES: stops;
array[COURIERS] of var 0..max(courier_sizes):courier_loads;
array[ITEMS] of var COURIERS:item_responsability; % wich courier delivers item k
var lower_bound..upper_bound:longest_trip;
array[COURIERS] of var 0..upper_bound:distances_traveled;

% constraints for the decision variable 

% capacity constraint. It also ensures uniqueness of the items delivers
constraint bin_packing_capa(courier_sizes,item_responsability,item_sizes);

% couriers have to start and end in default_val
constraint forall(i in COURIERS)(
    stops[i,1]=default_val
);
constraint forall(i in COURIERS)(
    stops[i,num_items+2]=default_val
);







% minimize the optimization variable
constraint longest_trip= max(distances_traveled);
solve :: seq_search([
  int_search(stops,first_fail, indomain_min),
  int_search(item_responsability,first_fail, indomain_min)
])minimize(longest_trip);


% output ["Stops:\n"] ++
%        [ show(stops[i,j])++ ", " ++ 
%          if j == num_items+2 then "\n" else "" endif |
%          i in COURIERS, j in 1..num_items+2 ]++["\n"];

% output ["Itinerary:\n"] ++
%        [ 
%         % if j==1 then "Start, " else "" endif ++
%         if fix(stops[i,j])==default_val then "" else show(stops[i,j])++", " endif ++ 
%         if j == num_items+2 then 
%           % "End"++
%           " --> Distance="++show(distances_traveled[i])++"\n" 
%         else "" endif
%         |i in COURIERS, j in 1..num_items+2
%        ];
       
  output["Obj: "++show(longest_trip)++"\n"];

% output["Picks:\n"]++[show(item_responsability)];

% output for the json, to be parsed in python:
output [ show(stops[i,j])++ "," ++ 
         if j == num_items+2 /\i!=num_couriers then "\n" endif |
         i in COURIERS, j in 1..num_items+2 ];
