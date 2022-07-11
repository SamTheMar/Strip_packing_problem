import numpy as np
from common.utils import Rectangle


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
    start = 0
    for r in rectangles:
        num_positions = (W-r.w+1)*(H-r.h+1)
        if verbose:
            print(r)
            print(start+1,'..',start+num_positions+1)
            print('=====================================')
        V.append(list(range(start+1,start+num_positions+1)))
        start = start+num_positions

    C = np.zeros((V[-1][-1], W*H), dtype='i1')

    for i in range(C.shape[0]):

        index = None
        circuit = None
        for k in range(len(rectangles)):
            if (i+1)>=V[k][0] and (i+1)<=V[k][-1]:
                index = i+1-V[k][0]
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