include "globals.mzn";

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
array[COURIERS] of var int: courier_loads;
% items size 
array[ITEMS] of int: item_sizes;
% matrix of distances between nodes
set of int:DELIVERS = 1..num_items-num_couriers+1;
array[NODES, NODES] of int: distances;

% bounds for the objective function
int:lower_bound;
int:upper_bound;

% total distance traveled by each courier
array[COURIERS] of var 0..upper_bound: distances_traveled;
% largest distance among all couriers
var lower_bound..upper_bound: longest_trip;

% mip part
array[NODES,NODES,COURIERS] of var 0..1: x;


%%%%%%% CONSTRAINT FOR DECISION VARIABLES %%%%%%%%
% distance computation
constraint forall(c in COURIERS)(
        distances_traveled[c]=sum([distances[i,j]*x[i,j,c]*(i!=j)  |i,j in NODES])
);
% only one visit per item location
constraint forall(j in ITEMS)(
    1=sum([x[i,j,c]*(i!=j)  |i in NODES, c in COURIERS])
);
constraint forall(i in ITEMS)(
    1=sum([x[i,j,c]*(i!=j)  |j in NODES, c in COURIERS])
);
% depart and arrive on the depot
constraint forall(c in COURIERS)(
    1=sum([x[i,num_items+1,c]  |i in ITEMS]) /\
    1=sum([x[num_items+1,j,c]  |j in ITEMS])
);
% number of vehicles coming in and out of a item location is the same
constraint forall(c in COURIERS)(
    forall(j in NODES)(
        sum([x[i,j,c]*(i!=j)|i in NODES])-
        sum([x[j,i,c]*(i!=j)|i in NODES])=0
    )
);
% bin packing
constraint forall(c in COURIERS)(
    courier_loads[c]=sum([item_sizes[j]*x[i,j,c]*(i!=j)|i in NODES,j in ITEMS])
);
constraint forall(c in COURIERS)(
    courier_loads[c]<=courier_capacities[c]
);
% mtz
array[NODES,COURIERS] of var DELIVERS:u;
constraint forall(c in COURIERS) (
    forall(i in ITEMS) (
        forall(j in ITEMS) (
            (i != j) -> 
            (u[i, c] - u[j, c] + 1<=(num_items - 1) * (1 - x[i, j, c]))
        )
    )
);

%%%%%%%%%%%%%%%%%%% OBJECTIVE %%%%%%%%%%%%%%%%%%%%
constraint longest_trip = max(distances_traveled);
solve :: seq_search([
%   int_search(x,first_fail, indomain_random),
%   float_search(u, 0.01,first_fail, indomain_split),
  int_search([longest_trip], first_fail, indomain_min)
])minimize(longest_trip);


%%%%%%%%%%%%%%%% OUTPUT UTILITIES %%%%%%%%%%%%%%%%
output ["x_c1:\n"] ++
       [ show(x[i,j,1])++ 
         if j == num_items+1 then "\n" else ", " endif |
         i in NODES, j in NODES]++["\n"];
output ["x_c2:\n"] ++
       [ show(x[i,j,2])++ 
         if j == num_items+1 then "\n" else ", " endif |
         i in NODES, j in NODES]++["\n"];

output ["Itinerary:\n"] ++
       [ 
%         % if j==1 then "Start, " else "" endif ++
%         if fix(stops[i,j])==depot then "" else show(stops[i,j])++", " endif ++ 
%         if j == num_items then 
%           % "End"++
          " --> Distance="++show(distances_traveled[c])++
          "; Load="++show(courier_loads[c])++
          "\n" 
%         else "" endif
        |c in COURIERS
       ];
 
output [show(u[i,j])++if j==num_couriers then "\n" else ", " endif|i in NODES, j in COURIERS];

output["Obj: "++show(longest_trip)++"\n"];