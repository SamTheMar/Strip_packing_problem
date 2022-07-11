int: W;
int: H;

int: nCircuits;
int: nPositions;
int: nTiles;

set of int: CIRCUITS = 1..nCircuits;
set of int: POSITIONS = 1..nPositions;
set of int: TILES = 1..nTiles;


array[POSITIONS,TILES] of 0..1: C;
array[0..nCircuits] of int: V;

array[CIRCUITS,POSITIONS] of var 0..1: x;

constraint forall(p in TILES)(sum([C[j,p]*x[i,j]|i in CIRCUITS, j in V[i-1]+1..V[i]])<=1);

constraint forall(i in CIRCUITS)(sum([x[i,j]|j in V[i-1]+1..V[i]])=1);

constraint forall(i in CIRCUITS)(sum([x[i,j]|j in POSITIONS diff V[i-1]+1..V[i]])=0);

constraint sum([C[j,p]*x[i,j]|i in CIRCUITS, j in V[i-1]+1..V[i], p in TILES])<=W*H;

solve minimize 0;