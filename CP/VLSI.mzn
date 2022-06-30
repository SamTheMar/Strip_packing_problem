include "globals.mzn";

int: w; % width of the silicon plate
int: t; % number of circuits
array[1..t,1..2] of int: tDim; % dimensions of the circuits

int: max_length = sum([tDim[i,2]| i in 1..t]);
int: min_length = max([tDim[i,2]| i in 1..t]);

var min_length..max_length: l; % length of the silicon plate
% positions of the circuits
array[1..t] of var 0..w: x;
array[1..t] of var 0..max_length: y;

constraint diffn(x, y, [tDim[i,1]| i in 1..t], [tDim[i,2]| i in 1..t])::domain; % no box overlap

constraint forall(i in 1..t)(y[i]+tDim[i,2]<=l/\x[i]+tDim[i,1]<=w);


array[0..w] of var set of 1..t: columns;

constraint forall(v in 0..w)(columns[v]={i | i in 1..t where v in x[i]..x[i]+tDim[i,1]-1});

%solve satisfy;
solve minimize l;

output [show(w)++" "++show(l)++"\n"]++
       [show(t)++"\n"]++
       [show(tDim[i,1])++" "++show(tDim[i,2])++" "++show(x[i])++" "++show(y[i])++"\n"|i in 1..t]
       