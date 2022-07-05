import sys
sys.path.append('./common')
from utils import read_instance,Rectangle
import math
import numpy as np

from datetime import timedelta
from minizinc import Instance, Model, Solver

def validPositions(rectangles,W,H, verbose=False):
    V = []
    start = 0
    for r in rectangles:
        num_positions = (W-r.w+1)*(H-r.h+1)
        #print(num_positions)
        if verbose:
            print(r)
            print(start+1,'..',start+num_positions+1)
            print('=====================================')
        V.append(list(range(start+1,start+num_positions+1)))
        start = start+num_positions

    C = np.zeros((V[-1][-1], W*H), dtype='int')

    for i in range(C.shape[0]):

        index = None
        circuit = None
        for k in range(len(rectangles)):
            try:
                if index == None:
                    index = V[k].index(i+1)
                    circuit = k
            except:
                pass

        x = index // ((W - rectangles[circuit].w)+1)
        y = index % ((W - rectangles[circuit].w)+1)
        tiles = [(x+j)*W+y+1+k for j in range(rectangles[circuit].h) for k in range(rectangles[circuit].w)]

        if verbose:
            print(i+1)
            print(tiles)
            print("===================================")

        for tile in tiles:
            C[i,tile-1] = 1

    return V,C

W, n, rectangles = read_instance('./instances/ins-1.txt')

H=8

V, C = validPositions(rectangles,W,H)

timeout = timedelta(seconds=300) #300

model = Model("./LP/VLSI_LP.mzn") # modify search and restart strategy in the model file
solver = Solver.lookup("coin-bc") # cbc, coinbc

instance = Instance(solver, model)
instance["W"] = W
instance["H"] = H
instance["nCircuits"] = n
instance["nPositions"] = C.shape[0]
instance["nTiles"] = C.shape[1]
instance["C"] = C
instance["V"] = [0 if i<0 else V[i][-1] for i in range(-1,len(rectangles))]

print(W)
print(H)
print(n)
print(C.shape[0])
print(C.shape[1])
print(C)
print([0 if i<0 else V[i][-1] for i in range(-1,len(rectangles))])

result = instance.solve(timeout=timeout)
print(result.solution)