#from curses.textpad import rectangle
import sys
sys.path.append('./')
from common.utils import read_instance,save_solution,PositionedRectangle,Rectangle,write_execution_time
import math
import numpy as np

from datetime import timedelta
from minizinc import Instance, Model, Solver
from time import time

def filterValidPositionBC(rectangles,V,W,H):
    bc = np.argmax([r.w*r.h for r in rectangles])
    bc_pos = [((j-V[bc][0])%(W-rectangles[bc].w+1),H-(j-V[bc][0])//(W-rectangles[bc].w+1)-rectangles[bc].h) for j in V[bc]]
    valid_bc_pos = [i+V[bc][0] for i in range(len(bc_pos)) if bc_pos[i][0]<=(W-rectangles[bc].w)//2 and bc_pos[i][1]<=(H-rectangles[bc].h)//2]
    return valid_bc_pos

def validPositions(rectangles,W,H, verbose=False):
    V = []
    #V = [0]
    start = 0
    for r in rectangles:
        num_positions = (W-r.w+1)*(H-r.h+1)
        #print(num_positions)
        if verbose:
            print(r)
            print(start+1,'..',start+num_positions+1)
            print('=====================================')
        V.append(list(range(start+1,start+num_positions+1)))
        #V.append(start+num_positions+1)
        start = start+num_positions

    C = np.zeros((V[-1][-1], W*H), dtype='int16')
    #C = np.zeros((V[-1], W*H), dtype='int16')

    for i in range(C.shape[0]):

        index = None
        circuit = None
        for k in range(len(rectangles)):
            if (i+1)>=V[k][0] and (i+1)<=V[k][-1]:
            #if (i+1)>=V[k-1]+1 and (i+1)<=V[k]:
                index = i+1-V[k][0]
                #index = i-V[k-1]
                circuit = k
                break

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

def createAssoc(rectangles,H,W):
    notAssoc = set()
    assoc = []
    new_circuits = []
    for i in range(len(rectangles)):
        r = rectangles[i]
        if r.w == r.h or r.w > H or r.h > W:
            notAssoc.add(i+1)
        else:
            rassoc = [j+1 for j in range(len(rectangles)) if j!=i and r.w==rectangles[j].h and  r.h==rectangles[j].w]
            if rassoc and rassoc[0]>i+1:
                    assoc.append([i+1,rassoc[0],2])
            elif not(rassoc):
                new_circuits.append(Rectangle(r.h,r.w))
                assoc.append([i+1,len(rectangles)+len(new_circuits),1])
    rectangles.extend(new_circuits)
    return np.array(assoc),notAssoc
    


def solve_LP(instance_num, ordering = False, rotation = True):
    
    input_url = './instances/ins-%d.txt'%instance_num
    if rotation:
        output_url = "./LP/out/rotation/txt/ins-%d-sol.txt"%instance_num
    else:
        output_url = "./LP/out/no_rotation/txt/ins-%d-sol.txt"%instance_num

    W, n, rectangles = read_instance(input_url)

    H = math.ceil(sum([rectangles[i].w * rectangles[i].h for i in range(n)])/W)-1

    timeout = timedelta(seconds=300) #300

    if rotation:
        model = Model("./LP/VLSI_rotation_LP.mzn")
    else:
        model = Model("./LP/VLSI_LP.mzn")
    solver = Solver.lookup('gurobi') # coin-bc, cbc, coinbc

    instance = Instance(solver, model)
    instance["W"] = W
    if rotation:
        assoc,notAssoc = createAssoc(rectangles,H,W)
        #print(rectangles)
        #print(assoc)
        #print(notAssoc)
        instance["nCircuits"] = len(rectangles)
        instance["nAssoc"] = assoc.shape[0]
        instance["assoc"] = assoc
        instance["notAssoc"] = notAssoc
    else:
        instance["nCircuits"] = n

    if ordering:
        rectangles = [rectangles[i] for i in np.argsort([r.w*r.h for r in rectangles])[::-1]]

    start_time = time()
    feasible = False
    counter = 0
    while not(feasible) and time()-start_time<=300:

        counter = counter + 1
        H = H + 1

        V, C = validPositions(rectangles,W,H)
        #print(H)
        #print(V)

        #print(filterValidPositionBC(rectangles,V,W,H))
        
        instance["H"] = H
        instance["nPositions"] = C.shape[0]
        instance["nTiles"] = C.shape[1]
        instance["C"] = C
        instance["V"] = [0 if i<0 else V[i][-1] for i in range(-1,len(rectangles))]
        #instance["V"] = V
        if not(rotation):
            instance["bc"] = 1 if ordering else np.argmax([r.w*r.h for r in rectangles])+1
            instance["filteredPosBC"] = set(filterValidPositionBC(rectangles,V,W,H))

        inner_start_time = time()
        result = instance.solve(timeout=timeout)
        inner_execution_time = time()-inner_start_time
        feasible = not(str(result.status)=="UNSATISFIABLE")

    if counter == 1:
        execution_time = inner_execution_time
    else:
        execution_time = time()-start_time
    if feasible and execution_time <=300:
        x = result.solution.x
        positioned_rectangles = []
        for i in range(len(rectangles)):
            if rotation and not(1 in x[i]):
                continue
            if rotation:
                indexes = [j+1-V[i][0] for j in range(len(x[i])) if x[i][j]==1]
                pos = [(idx % ((W - rectangles[i].w)+1), H - idx // ((W - rectangles[i].w)+1) - rectangles[i].h) for idx in indexes]
                new_rectangles = [PositionedRectangle(p[0],p[1],rectangles[i].w,rectangles[i].h) for p in pos]
                positioned_rectangles.extend(new_rectangles)
            else:
                vpos = x[i].index(1)
                index = vpos + 1 - V[i][0]
                #index = vpos - V[i-1]
                pos = (index % ((W - rectangles[i].w)+1), H - index // ((W - rectangles[i].w)+1) - rectangles[i].h)
                positioned_rectangles.append(PositionedRectangle(pos[0],pos[1],rectangles[i].w,rectangles[i].h))

            #print(rectangles[i], pos)

        save_solution(output_url,W,H,positioned_rectangles)
        write_execution_time(output_url, execution_time)
        print(instance_num,"solved")
    else:
        print(instance_num,"not solved")

for instance_num in range(1,40):
    solve_LP(instance_num)