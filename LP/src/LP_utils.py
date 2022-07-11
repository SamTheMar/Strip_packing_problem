import numpy as np
from common.utils import Rectangle

def filterValidPositionBC(rectangles,V,W,H):
    bc = np.argmax([r.w*r.h for r in rectangles])
    bc_pos = [((j-V[bc][0])%(W-rectangles[bc].w+1),H-(j-V[bc][0])//(W-rectangles[bc].w+1)-rectangles[bc].h) for j in V[bc]]
    valid_bc_pos = [i+V[bc][0] for i in range(len(bc_pos)) if bc_pos[i][0]<=(W-rectangles[bc].w)//2 and bc_pos[i][1]<=(H-rectangles[bc].h)//2]
    return valid_bc_pos


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
    return assoc,notAssoc

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

    C = np.zeros((V[-1][-1], W*H), dtype='i1')
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