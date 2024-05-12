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
array[COURIERS,ITEMS] of var int: delivers;

% constraint per il peso
% constraint forall(c in COURIERS)(
%     % prendo gli elementi diversi da zero per ogni corriere,
%     % quegli elementi sono gli indici degli item che deve consegnare    
%     % poi itero su quegli indici e controllo che la somma sia minore di itemsize
%     sum(j in ITEMS where delivers[c, j] != 0)(item_sizes[j]) <= courier_sizes[c]
% );

% constraint un item può essere consegnato solo da un corriere
% constraint un corriere consegni solo una volta un certo item
% constraint all_different_except_0(delivers)::domain;

% constraint che tutti i pacchi sono consegnati
% constraint forall(j in ITEMS)(
%     member({delivers[i, j_] | i in COURIERS,j_ in ITEMS},j)
% );
constraint nvalue(num_items+1, delivers);
% predicate nvalue(var int: n, array [$X] of var int: x)

% 2.  predicate nvalue(var int: n, array [$X] of var opt int: x)

% 3.  function var int: nvalue(array [$X] of var int: x)

% 4.  function var int: nvalue(array [$X] of var opt int: x)

% 1, 2.

%     Requires that the number of distinct values in x is n.
% 3, 4.

%     Returns the number of distinct values in x.

% 0 3 3 6 5 6 6 2
% 3 0 4 3 4 7 7 3
% 3 4 0 7 6 3 5 3
% 6 3 7 0 3 6 6 4
% 5 4 6 3 0 3 3 3
% 6 7 3 6 3 0 2 4
% 6 7 5 6 3 2 0 4
% 2 3 3 4 3 4 4 0

% constraint per distribuire il lavoro tra i corrieri
% minimizzare l'ultimo corriere
% var int:0..-bho-:longest_trip 
% solve ::  -qualcosa- minimize longest_trip

 output ["Delivers:\n"] ++
       [ show(delivers[i,j]) ++ ", " ++ 
         if j == num_items then "\n" else "" endif |
         i in COURIERS, j in ITEMS ];
