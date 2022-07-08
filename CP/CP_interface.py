from datetime import timedelta
from minizinc import Instance, Model, Solver
from time import time

import sys
sys.path.append("./")
from common.utils import write_execution_time,read_instance

import numpy as np
import math

timeout = timedelta(seconds=300) #300

rotation = True
ordering = True

if rotation:
    model_url = "./CP/VLSI_Rotation_CP.mzn"
else:
    model_url = "./CP/VLSI_CP.mzn"

model = Model(model_url)
solver = Solver.lookup("chuffed")

for ss in range(1, 4):
    for rs in range(1,4):
        for instance_num in range(1,2):
            input_url = './instances/ins-%d.txt'%instance_num
            output_url = './CP/out'
            if rotation:
                output_url = output_url + '/rotation'
            else:
                output_url = output_url + '/no_rotation'
            if rs == 1:
                output_url = output_url + '/luby'
            elif rs == 2:
                output_url = output_url + '/geometric'
            else:
                output_url = output_url + '/no_restart'
            if ss == 1:
                output_url = output_url + '/dom_w_deg'
            elif ss == 2:
                output_url = output_url + '/impact'
            else:
                output_url = output_url + '/non_increasing_area'
            output_url = output_url + '/ins-%d-sol.txt'%instance_num

            instance = Instance(solver, model)

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
            instance["search_heuristic"] = ss # 1 dom_deg, 2 impact, 3 input_order
            instance["restart_strategy"] = rs # 1 luby(150), 2 geometric(2,50), 3 niente

            try:
                start_time = time()
                result = instance.solve(timeout=timeout)
                execution_time = time()-start_time

                with open(output_url, "w") as f:
                    f.write(str(result))
                write_execution_time(output_url, execution_time)

                print(instance_num,"solved")
            except:
                print(instance_num,"not solved")
