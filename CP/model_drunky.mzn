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

% constraints for the decision variable 

% couriers have to start and end in default_val
constraint forall(i in COURIERS)(
    stops[i,1]=default_val
);
constraint forall(i in COURIERS)(
    stops[i,num_items+2]=default_val
);


array[ITEMS] of var COURIERS:item_responsability; % wich courier delivers item k
% capacity constraint. It also ensures uniqueness of the items delivers
constraint bin_packing_capa(courier_sizes,item_responsability,item_sizes);

% each courier delivers something
constraint forall(i in COURIERS)(
    count(item_responsability, i) > 0
);

% link stops and item_responsability
constraint forall(i in ITEMS)(
  forall(c in COURIERS)(
    if c==item_responsability[i] then
    member(row(stops,c),i) 
    else stops[c,i+1]=stops[c,i] endif
  )
);

% calculate the load for each courier
array[COURIERS] of var 0..max(courier_sizes):courier_loads;

constraint forall(c in COURIERS)(
  courier_loads[c]=sum(i in ITEMS where item_responsability[i]==c)(item_sizes[i])
);

% link courier_loads and stops to carry the same weight
constraint forall(c in COURIERS)(
  courier_loads[c]=sum(i in ITEMS where member(row(stops,c),i))(item_sizes[i])
);

% if a courier has bigger capacity, it will deliver more weight
constraint forall(c in 1..num_couriers-1)(
  if courier_sizes[c]>courier_sizes[c+1] then
  courier_loads[c]>courier_loads[c+1] endif
);

array[COURIERS] of var 0..upper_bound:distances_traveled;

% Compute total distance
constraint forall(c in COURIERS)(
  distances_traveled[c] = sum(j in NODES)(distances[stops[c,j], stops[c,j+1]])
);

% minimize the optimization variable
var lower_bound..upper_bound:longest_trip;
constraint longest_trip= max(distances_traveled);
solve :: seq_search([
  int_search(stops,indomain_random, indomain_min),
  int_search(item_responsability,indomain_random, indomain_min)
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
