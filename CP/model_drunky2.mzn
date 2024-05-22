include "bin_packing_capa.mzn";
include "member.mzn";
include "count.mzn";
include "increasing.mzn";
include "decreasing.mzn";
include "nvalue.mzn";
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

array[COURIERS, 1..num_items+2] of var NODES: stops;
array[ITEMS] of var COURIERS:item_responsability; % wich courier delivers item k
var 0..upper_bound:longest_trip;
array[COURIERS] of var 0..upper_bound:distances_traveled;


% couriers have to start and end in default_val
constraint forall(i in COURIERS)(
    stops[i,1]=default_val
);
constraint forall(i in COURIERS)(
    stops[i,num_items+2]=default_val
);
constraint forall(c in COURIERS)(
  stops[c,2]!=default_val
);
constraint forall(i in ITEMS)(
  count(stops,i,1)
)::domain;

% padding of the stops
  % count(item_responsability,c) -->numero di item che devono stare sulla riga
constraint forall(c in COURIERS)(
  forall(i in ITEMS)(
    (i<=count(item_responsability,c)) <-> ( stops[c,i+1]!=default_val)
))::domain;

constraint forall(c in COURIERS,i in ITEMS)(
  if item_responsability[i]==c then
  member(row(stops,c),i) endif
)::domain;

constraint nvalue(num_couriers, item_responsability);
% capacity constraint. It also ensures uniqueness of the items delivered
constraint bin_packing_capa(courier_sizes,item_responsability,item_sizes)::domain;

% Compute total distance
% constraint forall(c in COURIERS)(
%    distances_traveled[c] = sum([distances[stops[c,i],stops[c,i+1]] | i in ITEMS])
% %    constraint distances_traveled[1] = sum([distances[stops[1,i],stops[1,i+1]] | i in ITEMS]);
% );



% minimize the optimization variable
solve
::seq_search([
    int_search(item_responsability,first_fail,indomain_random),
    int_search(stops,first_fail,indomain_random),
%     int_search([longest_trip],smallest,indomain_min)
])  
% minimize longest_trip;
satisfy;

% constraint forall(c in 1..num_couriers-1)(
%     courier_loads[c] >= courier_loads[c+1]
% );

% constraint forall(c in COURIERS)(
%   courier_loads[c]=sum(i in ITEMS where item_responsability[i]==c)(item_sizes[i])
% );


% output ["Stops:\n"] ++
%        [ show(stops[i,j])++ ", " ++ 
%          if j == num_items+2 then "\n\n" else "" endif |
%          i in COURIERS, j in 1..num_items+2 ]++["\n"];

% output ["Itinerary:\n"] ++
%        [ 
%         % if j==1 then "Start, " else "" endif ++
%         if fix(stops[i,j])==default_val then "" else show(stops[i,j])++", " endif ++ 
%         if j == num_items+2 then 
%           % "End"++
%           " --> Distance="++show(distances_traveled[i])++", size:"++ show(courier_sizes[i])++"/"++show(courier_loads[i])++"\n" 
%         else "" endif
%         |i in COURIERS, j in 1..num_items+2
%        ];
       
% output["Obj: "++show(longest_trip)++"\n"];

% output["Picks:\n"]++[show(item_responsability)++"\n"];