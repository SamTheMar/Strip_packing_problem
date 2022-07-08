%libraries
include "globals.mzn";

int: w;
int: n;
int: minH;
int: maxH;

set of int: CIRCUITS = 1..n;

% biggest circuit and second biggest circuit
CIRCUITS: bc;
CIRCUITS: sbc;

array[CIRCUITS] of int: dimX;
array[CIRCUITS] of int: dimY;

int: search_heuristic = 3; % 1 dom_deg, 2 impact, 3 indomain_order
int: restart_strategy = 2; % 1 luby 150, 2 geometric 2 50, 3 niente                    

array [CIRCUITS] of var 0..w-min([dimX[i]| i in CIRCUITS]): x;
array [CIRCUITS] of var 0..maxH-min([dimY[i]| i in CIRCUITS]): y;

var minH..maxH: l = max(i in CIRCUITS)(y[i] + dimY[i]);

%overlap constrains
constraint diffn(x, y, [dimX[i]|i in CIRCUITS], [dimY[i]| i in CIRCUITS]) :: domain;
constraint forall (i in CIRCUITS) (x[i] + dimX[i] <= w);
constraint forall (i in CIRCUITS) (y[i] + dimY[i] <= l);

% implied constraints
%??????????????????????????????????????? see the others solutions
constraint cumulative(x, [dimX[i]| i in CIRCUITS], [dimY[i]| i in CIRCUITS], l) :: domain;
constraint cumulative(y, [dimY[i]| i in CIRCUITS], [dimX[i]| i in CIRCUITS], w) :: domain;

% CIRCUITS which can't stay one of the side of the other are up or down
constraint forall(i,j in CIRCUITS where j>i)(
if dimX[i]+dimX[j]>w then y[i]<y[j] -> y[i]+dimY[i]<=y[j] /\ y[j]<y[i]-> y[j]+dimY[j]<=y[i] endif);

/*
constraint forall(i,j in CIRCUITS where j>i)(
dimY[i]+dimY[j]>l -> (x[i]<x[j] -> x[i]+dimX[i]<=x[j] /\ x[j]<x[i]-> x[j]+dimX[j] <=x[i]));
*/

% rows and columns symmetry
constraint symmetry_breaking_constraint(
    forall (i,j in CIRCUITS where i < j) ((x[i] == x[j] /\ dimX[i] == dimX[j]) -> y[i] <= y[j] - dimY[i]));
constraint symmetry_breaking_constraint(
    forall (i,j in CIRCUITS where i < j) ((y[i] == y[j] /\ dimY[i] == dimY[j]) -> x[i] <= x[j] - dimX[i]));

% CIRCUITS of the same dimensions
constraint symmetry_breaking_constraint(
forall(i,j in CIRCUITS where j>i)(if dimX[i]==dimX[j] /\ dimY[i]==dimY[j] then x[i]<=x[j] /\ y[i]<=y[j] endif));


% break symmetries for the biggest circuit
constraint symmetry_breaking_constraint(
x[1]<=(w-dimX[bc]) div 2 /\ y[1] <= (l-dimY[sbc]) div 2);
       
% three blocks symmetry
%??????????????????????????????????????????????????????????????????????????????????????????????' see others solution
constraint symmetry_breaking_constraint(
    forall (i,j,k in CIRCUITS where i > j /\ j > k)
        ((x[i] == x[j] /\ dimX[i] == dimX[j] /\ y[i] == y[k] /\ dimY[i] + dimY[j] == dimY[k]) -> x[k] <= x[i] ));
constraint symmetry_breaking_constraint(
    forall (i,j,k in CIRCUITS where i > j /\ j > k)
        ((y[i] == y[j] /\ dimY[i] == dimY[j] /\ x[i] == x[k] /\ dimX[i] + dimX[j] == dimX[k]) -> y[k] <= y[i] ));
        
% biggest circuit bottom left to second biggest circuit
constraint x[bc] <= x[sbc] /\ y[bc] <= y[sbc];

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
       [show(dimX[i])++" "++show(dimY[i])++" "++show(x[i])++" "++show(y[i])++"\n"|i in CIRCUITS];
       