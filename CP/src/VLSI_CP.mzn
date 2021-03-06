include "globals.mzn";

int: w;
int: n;
int: minH;
int: maxH;

set of int: CIRCUITS = 1..n;

% biggest item and second biggest item
CIRCUITS: bc;
CIRCUITS: sbc;

array[CIRCUITS] of int: dimX;
array[CIRCUITS] of int: dimY;

int: search_heuristic; % 1 dom_w_deg, 2 impact, 3 input_order
int: restart_strategy; % 1 luby(150), 2 geometric(2,50), 3 niente

array [CIRCUITS] of var 0..w-min([dimX[i]| i in CIRCUITS]): x;
array [CIRCUITS] of var 0..maxH-min([dimY[i]| i in CIRCUITS]): y;

var minH..maxH: l = max(i in CIRCUITS)(y[i] + dimY[i]);

% main problem constraints
constraint diffn(x, y, dimX, dimY) :: domain;
constraint forall (i in CIRCUITS) (x[i] + dimX[i] <= w);
constraint forall (i in CIRCUITS) (y[i] + dimY[i] <= l);

% implied constraints
constraint cumulative(x, dimX, dimY, l) :: domain;
constraint cumulative(y, dimY, dimX, w) :: domain;

% items which can't stay one of the side of the other are up or down
constraint forall(i,j in CIRCUITS where j>i)(
if dimX[i]+dimX[j]>w then y[i]<y[j] -> y[i]+dimY[i]<=y[j] /\ y[j]<y[i]-> y[j]+dimY[j]<=y[i] endif);

% items which can't stay one on top of the other are one to the side of the other
constraint forall(i,j in CIRCUITS where j>i)(
dimY[i]+dimY[j]>l -> (x[i]<x[j] -> x[i]+dimX[i]<=x[j] /\ x[j]<x[i]-> x[j]+dimX[j] <=x[i]));


% break symmetries for the biggest item
constraint symmetry_breaking_constraint(
x[bc]<=(w-dimX[bc]) div 2 /\ y[bc] <= (l-dimY[bc]) div 2);

% biggest item bottom left to second biggest item
constraint x[bc] <= x[sbc] /\ y[bc] <= y[sbc];

% row-item and column-item symmetry
constraint symmetry_breaking_constraint(
    forall (i,j in CIRCUITS where i < j) ((x[i] == x[j] /\ dimX[i] == dimX[j]) -> y[i] <= y[j] - dimY[i]));
constraint symmetry_breaking_constraint(
    forall (i,j in CIRCUITS where i < j) ((y[i] == y[j] /\ dimY[i] == dimY[j]) -> x[i] <= x[j] - dimX[i]));
    
% three items symmetry
constraint symmetry_breaking_constraint(
    forall (i,j,k in CIRCUITS where i > j /\ j > k)
        ((x[i] == x[j] /\ dimX[i] == dimX[j] /\ y[i] == y[k] /\ dimY[i] + dimY[j] == dimY[k]) -> x[k] <= x[i] ));
constraint symmetry_breaking_constraint(
    forall (i,j,k in CIRCUITS where i > j /\ j > k)
        ((y[i] == y[j] /\ dimY[i] == dimY[j] /\ x[i] == x[k] /\ dimX[i] + dimX[j] == dimX[k]) -> y[k] <= y[i] ));

% items of the same dimensions
constraint symmetry_breaking_constraint(
forall(i,j in CIRCUITS where j>i)(if dimX[i]==dimX[j] /\ dimY[i]==dimY[j] then x[i]<=x[j] /\ y[i]<=y[j] endif));

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

output [show(w)++" "++show(l)++"\n"]++
       [show(n)++"\n"]++
       [show(dimX[i])++" "++show(dimY[i])++" "++show(x[i])++" "++show(y[i])++"\n"|i in CIRCUITS];
       