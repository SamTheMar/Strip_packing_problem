% Use this editor as a MiniZinc scratch book

int: W;
int: H;

int: nCircuits;
int: nPositions;
int: nAssoc;
int: nTiles;
%int: bc;

set of int: CIRCUITS = 1..nCircuits;
set of int: POSITIONS = 1..nPositions;
set of int: TILES = 1..nTiles;
set of int: ASSOC = 1..nAssoc;


array[POSITIONS,TILES] of 0..1: C;
array[0..nCircuits] of int: V;
array[ASSOC,1..3] of int: assoc;
%set of int: filteredPosBC; % togliere lui
set of int: notAssoc;

array[CIRCUITS,POSITIONS] of var 0..1: x;

constraint forall(p in TILES)(sum([C[j,p]*x[i,j]|i in CIRCUITS, j in V[i-1]+1..V[i]])<=1);

constraint forall(a in ASSOC)(
  sum([x[assoc[a,1],j] | j in V[assoc[a,1]-1]+1..V[assoc[a,1]]  ]) +
  sum([x[assoc[a,2],j] | j in V[assoc[a,2]-1]+1..V[assoc[a,2]]  ])
  = assoc[a,3]);
  
constraint forall(i in notAssoc)(sum([x[i,j]|j in V[i-1]+1..V[i]])=1);

%constraint sum([x[bc,j] | j in filteredPosBC])=1; % trovare le valid position anche per la rotazione

constraint sum([C[j,p]*x[i,j]|i in CIRCUITS, j in V[i-1]+1..V[i], p in TILES])<=W*H;

solve minimize 0;