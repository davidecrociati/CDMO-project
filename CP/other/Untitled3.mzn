include "globals.mzn";

% number of couriers
int: num_couriers;
set of int: COURIERS = 1..num_couriers;
% number of items
int: num_items;
set of int: ITEMS = 1..num_items;
% number of nodes(including the depot)
int: depot=num_items + 1;
set of int: NODES = 1..depot;

% couriers load capacity 
array[COURIERS] of int: courier_capacities;
% items size 
array[ITEMS] of int: item_sizes;
% matrix of distances between nodes
% set of int:DELIVERS = 1..num_items-num_couriers+1;
array[NODES, NODES] of int: distances;

%%%%%%%%%%%%%%% DECISION VARIABLES %%%%%%%%%%%%%%%
% route taken by each courier, represented as a sequence of nodes
array[NODES, NODES] of var 0..1: arcs;

% who is responsible for the delivery of a specific item
% array[ITEMS] of var COURIERS: item_responsibility;

% bounds for the objective function
int:lower_bound;
int:upper_bound;

% total distance traveled by each courier
array[COURIERS] of var 0..upper_bound: distances_traveled;
% largest distance among all couriers
var lower_bound..upper_bound: longest_trip;


%%%%%%% CONSTRAINT FOR DECISION VARIABLES %%%%%%%%
constraint arcs[depot,depot]=0;

constraint sum([arcs[depot,i]|i in ITEMS])=num_couriers;
constraint sum([arcs[i,depot]|i in ITEMS])=num_couriers;

constraint forall(i in ITEMS)(
  sum(row(arcs,i)<=1
);
constraint forall(i in ITEMS)(
  sum(column(arcs,i)<=1
);



% minimize the longest trip distance among all couriers
constraint longest_trip = max(distances_traveled);
solve :: seq_search([
%   int_search(stops, first_fail, indomain_min),
%   int_search(item_responsibility, first_fail, indomain_min),
  int_search([longest_trip], first_fail, indomain_min)
])
%       :: restart_luby(2)
minimize(longest_trip);



%%%%%%%%%%%%%%%% OUTPUT UTILITIES %%%%%%%%%%%%%%%%
% output ["Stops:\n"] ++
%        [ show(stops[i,j])++ 
%          if j == num_items then "\n" else ", " endif |
%          i in COURIERS, j in ITEMS ]++["\n"];

% output ["Itinerary:\n"] ++
%        [ 
%         % if j==1 then "Start, " else "" endif ++
%         if fix(stops[i,j])==depot then "" else show(stops[i,j])++", " endif ++ 
%         if j == num_items then 
%           % "End"++
%           " --> Distance="++show(distances_traveled[i])++"\n" 
%         else "" endif
%         |i in COURIERS, j in ITEMS
%        ];
       
% output["Obj: "++show(longest_trip)++"\n"];

% output for the json, to be parsed in python:
% output [ show(stops[i,j])++ "," ++ 
%          if j == num_items /\i!=num_couriers then "\n" endif |
%          i in COURIERS, j in ITEMS
%          ];