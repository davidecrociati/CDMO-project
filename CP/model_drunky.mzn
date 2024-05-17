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

% all items get delivered once 
% constraint forall(i in ITEMS)(
%   count(stops,i,1)
% );

% couriers have to start and end in default_val
constraint forall(i in COURIERS)(
    stops[i,1]=default_val
);
constraint forall(i in COURIERS)(
    stops[i,num_items+2]=default_val
);

% SIMMETRIES
% to avoid permutations we must ensure that there are no adjacent 'default_val' except 
% if they go until the end of the row
% constraint forall(i in COURIERS)(
%   forall(j in NODES)(
%     if stops[i,j]==stops[i,j+1]then
%       count(slice_1d(row(stops,i),[j+2..num_items+2],1..num_items+1-j),stops[i,j],num_items+1-j)
%     else true
%     endif
%   )
% );

array[ITEMS] of var COURIERS:item_responsability; % wich courier delivers item k
% capacity constraint. It also ensures uniqueness of the items delivers
constraint bin_packing_capa(courier_sizes,item_responsability,item_sizes);

constraint forall(i in COURIERS)(
    count(item_responsability, i) > 0
);

% channeling stops and item_responsability
constraint forall(j in ITEMS)(
    forall(i in COURIERS)(
        if i==item_responsability[j] then
            stops[i,j+1]=j
        else stops[i,j+1]=stops[i,j] endif
    )
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
       
% output["Obj: "++show(longest_trip)++"\n"];

% output["Picks:\n"]++[show(item_responsability)];