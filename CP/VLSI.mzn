%libraries
include "globals.mzn";

int: w;
int: n;
set of int: circuits = 1..n;
array[circuits,1..2] of int: dims;

int: search_heuristic = 1; % 1 dom_deg, 2 impact, 3 indomain_order
int: restart_strategy = 2; % 1 luby 150, 2 geometric 2 50, 3 niente

array[circuits] of int: ordering = arg_sort([dims[i,1]*dims[i,2]|i in circuits]);
array[circuits,1..2] of int: odims = array2d(circuits,1..2,[dims[ordering[n+1-i],j]|i in circuits, j in 1..2]);

int: minH = ceil((sum(i in circuits)(odims[i,1]*odims[i,2]))/w);
int: maxH = ceil(let {int: xmax=max(j in circuits)(odims[j,1])} in 
                    sum(i in circuits)(xmax*odims[i,2])/w);
                    
% biggest circuit and second biggest circuit
circuits: bc = 1;
circuits: sbc = 2;

array [circuits] of var 0..w-min([odims[i, 1]| i in circuits]): x;
array [circuits] of var 0..maxH-min([odims[i, 2]| i in circuits]): y;

var minH..maxH: l = max(i in circuits)(y[i] + odims[i,2]);

%overlap constrains
constraint diffn(x, y, [odims[i, 1]|i in circuits], [odims[i, 2]| i in circuits]) :: domain;
constraint forall (i in circuits) (x[i] + odims[i, 1] <= w);
constraint forall (i in circuits) (y[i] + odims[i, 2] <= l);

% implied constraints
%??????????????????????????????????????? see the others solutions
constraint cumulative(x, [odims[i, 1]| i in circuits], [odims[i, 2]| i in circuits], l) :: domain;
constraint cumulative(y, [odims[i, 2]| i in circuits], [odims[i, 1]| i in circuits], w) :: domain;

% circuits which can't stay one of the side of the other are up or down
constraint forall(i,j in circuits where j>i)(
if odims[i,1]+odims[j,1]>w then y[i]<y[j] -> y[i]+odims[i,2]<=y[j] /\ y[j]<y[i]-> y[j]+odims[j,2]<=y[i] endif);


constraint forall(i,j in circuits where j>i)(
odims[i,2]+odims[j,2]>l -> (x[i]<x[j] -> x[i]+odims[i,1]<=x[j] /\ x[j]<x[i]-> x[j]+odims[j,1] <=x[i]));




% rows and columns symmetry
constraint symmetry_breaking_constraint(
    forall (i,j in circuits where i < j) ((x[i] == x[j] /\ odims[i, 1] == odims[j, 1]) -> y[i] <= y[j] - odims[i,2]));
constraint symmetry_breaking_constraint(
    forall (i,j in circuits where i < j) ((y[i] == y[j] /\ odims[i, 2] == odims[j, 2]) -> x[i] <= x[j] - odims[i,1]));

% circuits of the same dimensions
constraint symmetry_breaking_constraint(
forall(i,j in circuits where j>i)(if odims[i,1]==odims[j,1] /\ odims[i,2]==odims[j,2] then x[i]<=x[j] /\ y[i]<=y[j] endif));


% break symmetries for the biggest circuit
constraint symmetry_breaking_constraint(
x[1]<=(w-odims[1,1]) div 2 /\ y[1] <= (l-odims[1,2]) div 2);
       
% three blocks symmetry
%??????????????????????????????????????????????????????????????????????????????????????????????' see others solution
constraint symmetry_breaking_constraint(
    forall (i,j,k in circuits where i > j /\ j > k)
        ((x[i] == x[j] /\ odims[i, 1] == odims[j, 1] /\ y[i] == y[k] /\ odims[i, 2] + odims[j, 2] == odims[k, 2]) -> x[k] <= x[i] ));
constraint symmetry_breaking_constraint(
    forall (i,j,k in circuits where i > j /\ j > k)
        ((y[i] == y[j] /\ odims[i, 2] == odims[j, 2] /\ x[i] == x[k] /\ odims[i, 1] + odims[j, 1] == odims[k, 1]) -> y[k] <= y[i] ));
        
% biggest circuit bottom left to second biggest circuit
constraint x[1] <= x[2] /\ y[1] <= y[2];

ann: search_ann_x =
if search_heuristic == 1 then
  int_search(x, dom_w_deg, indomain_min)
elseif search_heuristic == 2 then
  int_search(x, impact, indomain_min)
else
  int_search(x, input_order, indomain_min)
endif;

ann: search_ann_y =
if search_heuristic == 1 then
  int_search(y, dom_w_deg, indomain_min)
elseif search_heuristic == 2 then
  int_search(y, impact, indomain_min)
else
  int_search(y, input_order, indomain_min)
endif;

ann: restart_ann =
if restart_strategy == 1 then
  restart_luby(150)
elseif restart_strategy == 2 then
  restart_geometric(2, 50)
else
  restart_none
endif;

solve :: search_ann_x
      :: search_ann_y
      :: restart_ann
         minimize l;

%solve minimize l;

output [show(w)++" "++show(l)++"\n"]++
       [show(n)++"\n"]++
       [show(odims[i,1])++" "++show(odims[i,2])++" "++show(x[i])++" "++show(y[i])++"\n"|i in circuits];
       