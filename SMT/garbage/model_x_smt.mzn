include "member.mzn";
include "count.mzn";

% number of couriers
int: num_couriers;
set of int: COURIERS = 1..num_couriers;
% number of items
int: num_items;
set of int: ITEMS = 1..num_items;
% number of nodes(including the depot)
set of int: NODES = 1..num_items + 1;
int: depot=num_items + 1;

% couriers load capacity 
array[COURIERS] of int: courier_capacities;
% items size 
array[ITEMS] of int: item_sizes;
% matrix of distances between nodes
array[NODES, NODES] of int: distances;

%%%%%%%%%%%%%%% DECISION VARIABLES %%%%%%%%%%%%%%%
% route taken by each courier, represented as a sequence of nodes
array[COURIERS, 1..num_items + 2] of var NODES: stops;

% who is responsible for the delivery of a specific item
array[ITEMS] of var COURIERS: item_responsability;

% bounds for the objective function
int:lower_bound;
int:upper_bound;

% total distance traveled by each courier
array[COURIERS] of var 0..upper_bound: distances_traveled;
% largest distance among all couriers
var lower_bound..upper_bound: longest_trip;

% capacity constraint: the sum of item sizes assigned to each courier must not exceed the courier's capacity
constraint 
%       forall( i in ITEMS) (1 <= item_responsability[i] /\ item_responsability[i] <= num_couriers)
%     /\
      forall( c in COURIERS ) (
            courier_capacities[c] >= sum ( i in ITEMS ) (
                item_sizes[i] * ( item_responsability[i] = c )
            )
      );

% courier's routes have to start and end at the depot
constraint forall(i in COURIERS)(
    stops[i, 1] = depot
);

constraint forall(i in COURIERS)(
    stops[i, num_items+2] = depot
);

% each courier must be responsible for delivering at least one item
constraint forall(c in COURIERS)(
  member(item_responsability, c)
);

% each courier have to stop in at least one location different from the depot
constraint forall(c in COURIERS)(
  stops[c, 2]!=depot
);

% all items must be delivered(in theory it's already guaranteed by 'bin_packing_capa' but helps with the performances)
constraint forall(i in ITEMS)(
  count(stops, i, 1)
);

% channeling constraint: the number of items delivered by a courier in 'item_responsibility' matches the stops in 'stops'
constraint forall(c in COURIERS)(
  forall(i in ITEMS)(
    (i <= count(item_responsability, c)) -> (stops[c, i+1] != depot)
));
constraint forall(c in COURIERS)(
  forall(i in ITEMS)(
  (stops[c, i+1] != depot) -> (i <= count(item_responsability, c))
));

% all the items assigned to a courier in 'item_responsibility' must appear in the courier's route in 'stops'
constraint forall(c in COURIERS, i in ITEMS)(
  if item_responsability[i] == c then
  member(row(stops, c), i) endif
);


% compute total distances for each courier
% compute the successor nodes for each item to optimize distance calculation (accessing directly to distances[stops[c, i],  stops[c, i+1]] it's extremely slower)
% array[ITEMS] of var NODES:successors; 
% constraint forall(c in COURIERS)(
%   forall(i in 2..num_items+1)(
%     forall (j in ITEMS)(
%     not((stops[c, i] = depot) /\stops[c,i]=j /\ not(successors[j] = stops[c, i+1]))
%     )
%   )
% );
array[ITEMS] of var NODES:successors; 
constraint forall(c in COURIERS)(
  forall(i in 2..num_items+1)(
    if stops[c, i] != depot then
    successors[stops[c,i]] = stops[c, i+1] endif
  )
);

% the distance traveled by each courier is the sum of the distances between a node and its successor + the distance from the depot to the first item delivered
constraint forall(c in COURIERS)(
    distances_traveled[c] = sum(i in ITEMS)(distances[i, successors[i]] * (item_responsability[i] = c)) + distances[depot, stops[c, 2]]);

% minimize the longest trip distance among all couriers
constraint longest_trip= max(distances_traveled);
solve :: seq_search([
  int_search(stops,first_fail, indomain_random),
  int_search(item_responsability,first_fail, indomain_random),
  int_search([longest_trip],first_fail, indomain_min)
])minimize(longest_trip);



%%%%%%%%%%%%%%%% OUTPUT UTILITIES %%%%%%%%%%%%%%%%
% output ["Stops:\n"] ++
%        [ show(stops[i,j])++ ", " ++ 
%          if j == num_items+2 then "\n" else "" endif |
%          i in COURIERS, j in 1..num_items+2 ]++["\n"];

% output ["Itinerary:\n"] ++
%        [ 
%         % if j==1 then "Start, " else "" endif ++
%         if fix(stops[i,j])==depot then "" else show(stops[i,j])++", " endif ++ 
%         if j == num_items+2 then 
%           % "End"++
%           " --> Distance="++show(distances_traveled[i])++"\n" 
%         else "" endif
%         |i in COURIERS, j in 1..num_items+2
%        ];
       
% output["Obj: "++show(longest_trip)++"\n"];

% output for the json, to be parsed in python:
% output [ show(stops[i,j])++ "," ++ 
%          if j == num_items+2 /\i!=num_couriers then "\n" endif |
%          i in COURIERS, j in 1..num_items+2 ];
