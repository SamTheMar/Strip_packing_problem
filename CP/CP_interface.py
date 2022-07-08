from datetime import timedelta
from minizinc import Instance, Model, Solver
from time import time

import sys
sys.path.append("./")
from common.utils import write_execution_time,read_instance,save_solution

import numpy as np
import math

'''
import sys
sys.path.append('./')
from common.utils import read_instance,save_solution,PositionedRectangle,Rectangle,write_execution_time
'''



timeout = timedelta(seconds=300) #300

rotation = False
ordering = False

if rotation:
    model_url = "./CP/VLSI-Rotation.mzn"
else:
    model_url = "./CP/VLSI.mzn"
    #model_url = "./CP/VLSI_CP.mzn"

model = Model(model_url) # modify search and restart strategy in the model file
solver = Solver.lookup("chuffed")

time_tables = []

for instance_num in range(1,41):
    input_url = "./CP/CP_instances/ins-%d.dzn"%instance_num
    #input_url = './instances/ins-%d.txt'%instance_num
    if rotation:
        output_url = "./CP/CP_solutions_rotation/ins-%d-sol.txt"%instance_num
    else:
        output_url = "./CP/CP_solutions/ins-%d-sol.txt"%instance_num

    instance = Instance(solver, model)
    instance.add_file(input_url)

    '''
    W, n, rectangles = read_instance(input_url)

    if ordering:
        rectangles = [rectangles[i] for i in np.argsort([r.w*r.h for r in rectangles])[::-1]]

    bc = np.argmax([r.w*r.h for r in rectangles])
    sbc = np.argmax([rectangles[i].w*rectangles[i].h if i!=bc else 0 for i in range(len(rectangles))])

    minH = math.ceil(sum([r.w*r.h for r in rectangles])/W)
    maxDimX = max([r.w for r in rectangles])
    maxH = math.ceil(sum([maxDimX*r.h for r in rectangles])/W)

    instance["w"] = W
    instance["n"] = n
    instance["minH"] = minH
    instance["maxH"] = maxH
    instance["bc"] = bc+1
    instance["sbc"] = sbc+1
    instance["dimX"] = [r.w for r in rectangles]
    instance["dimY"] = [r.h for r in rectangles]
    '''

    try:
        start_time = time()
        result = instance.solve(timeout=timeout)
        execution_time = time()-start_time
        time_tables.append(execution_time)

        with open(output_url, "w") as f:
            f.write(str(result))
        write_execution_time(output_url, execution_time)

        print(instance_num,"solved")
    except:
        print(instance_num,"not solved")
