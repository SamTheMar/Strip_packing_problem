import getopt
import sys
sys.path.append('./')
from common.utils import read_instance,save_solution,PositionedRectangle,write_execution_time
from LP.LP_utils import *
import math
import numpy as np

from datetime import timedelta
from minizinc import Instance, Model, Solver
from time import time


def set_argv(argv):
    rotation = 'False'
    ordering = 'True'
    solver = 'gurobi'
    arg_help = "{0} -r <rotation> -o <ordering> -s <solver>".format(argv[0])
    error_arg = """Argument error:
    - rotation can be only True or False
    - ordering can be only True or False
    - solver can be only gurobi or coin-bc or cplex"""
    to_bool = {'False': False, 'True': True}

    try:
        opts, args = getopt.getopt(argv[1:],
                                   "hr:o:s:",
                                   ["help", "rotation=", "ordering=", "solver="])

    except:
        print(arg_help)
        sys.exit(2)

    for opt, arg in opts:
        if opt in ("-h", "--help"):
            print(arg_help)
            sys.exit(2)
        elif opt in ("-r", "--rotation"):
            if arg == 'False' or arg == 'True':
                rotation = arg
            else:
                print(error_arg)
                sys.exit(2)
        elif opt in ("-o", "--ordering"):
            if arg == 'False' or arg == 'True':
                ordering = arg
            else:
                print(error_arg)
                sys.exit(2)
        elif opt in ("-s", "--solver"):
            if arg == 'gurobi' or arg == 'coin-bc' or arg == 'cplex':
                solver = arg
            else:
                print(error_arg)
                sys.exit(2)

    return to_bool[rotation], to_bool[ordering], solver


def solve_LP(instance_num, ordering = False, rotation = True, solver = 'gurobi'):
    
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
    solver = Solver.lookup(solver) # coin-bc, cbc, coinbc

    instance = Instance(solver, model)
    instance["W"] = W

    if rotation:
        assoc,notAssoc = createAssoc(rectangles,H,W)
        instance["nCircuits"] = len(rectangles)
    else:
        instance["nCircuits"] = n

    if ordering:
        order = list(np.argsort([r.w*r.h for r in rectangles]))[::-1]
        rectangles = [rectangles[i] for i in order]
        if rotation:
            notAssoc = {order[i-1]+1 for i in notAssoc}
            assoc = [[order[a[0]-1]+1,order[a[1]-1]+1,a[2]] for a in assoc]
    if rotation:
        instance["assoc"] = np.array(assoc)
        instance["notAssoc"] = notAssoc
        instance["nAssoc"] = len(assoc)

    start_time = time()
    feasible = False
    counter = 0
    while not(feasible) and time()-start_time<=300:

        counter = counter + 1
        H = H + 1

        V, C = validPositions(rectangles,W,H)
        
        instance["H"] = H
        instance["nPositions"] = C.shape[0]
        instance["nTiles"] = C.shape[1]
        instance["C"] = C
        instance["V"] = [0 if i<0 else V[i][-1] for i in range(-1,len(rectangles))]
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
                pos = (index % ((W - rectangles[i].w)+1), H - index // ((W - rectangles[i].w)+1) - rectangles[i].h)
                positioned_rectangles.append(PositionedRectangle(pos[0],pos[1],rectangles[i].w,rectangles[i].h))

        save_solution(output_url,W,H,positioned_rectangles)
        write_execution_time(output_url, execution_time)
        print(instance_num,"solved")
    else:
        print(instance_num,"not solved")


if __name__ == "__main__":
    rotation, ordering, solver = set_argv(sys.argv)
    
    print(f"""Solving CP instance with
    - rotation: {rotation}
    - ordering: {ordering}
    - solver: {solver}\n""")

    for instance_num in range(1,41):
        solve_LP(instance_num, ordering=ordering, rotation=rotation, solver=solver)
