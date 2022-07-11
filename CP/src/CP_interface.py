import numpy as np
import math
import os
import getopt
from datetime import timedelta
from minizinc import Instance, Model, Solver
from time import time

import sys
sys.path.append("./")
from common.utils import write_execution_time,read_instance


def set_argv(argv):
    rotation = 'False'
    ordering = 'True'
    search_strategy = 'input_order'
    restart_strategy = 'luby'
    arg_help = "{0} -r <rotation> -o <ordering> -s <search_strategy> -t <restart_strategy>".format(argv[0])
    error_arg = """Argument error:
    - rotation can be only True or False
    - ordering can be only True or False
    - search_strategy can be only dom_w_deg, impact, input_order
    - restart_strategy can be only luby, geometric, none"""
    to_number = {'dom_w_deg': 1, 'impact': 2, 'input_order': 3,
                 'luby': 1, 'geometric': 2, 'none': 3}
    to_bool = {'False': False, 'True': True}
    
    try:
        opts, args = getopt.getopt(argv[1:], 
                                   "hr:o:s:t:", 
                                    ["help", "rotation=", "ordering=", "search_strategy=", "restart_strategy="])

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
        elif opt in ("-s", "--search_strategy"):
            if arg == 'dom_w_deg' or arg == 'impact' or arg == 'input_order':
                search_strategy = arg
            else:
                print(error_arg)
                sys.exit(2)
        elif opt in ("-t", "--restart_strategy"):
            if arg == 'luby' or arg == 'geometric' or arg == 'none':
                restart_strategy = arg
            else:
                print(error_arg)
                sys.exit(2)
    
    return to_bool[rotation], to_bool[ordering], to_number[search_strategy], to_number[restart_strategy]


if __name__ == "__main__":
    search_strategy = ['dom_w_deg', 'impact', 'input_order']
    restart_strategy = ['luby', 'geometric', 'none']
    rotation, ordering, ss, rs = set_argv(sys.argv)

    print(f"""Solving CP instance with
    - rotation: {rotation}
    - ordering: {ordering}
    - search_strategy: {search_strategy[ss-1]}
    - restart_strategy: {restart_strategy[rs-1]}\n""")

    timeout = timedelta(seconds=300) #300

    if rotation:
        model_url = "./CP/src/VLSI_rotation_CP.mzn"
    else:
        model_url = "./CP/src/VLSI_CP.mzn"

    model = Model(model_url)
    solver = Solver.lookup("chuffed")


    for instance_num in range(1,41):
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
        
        if not os.path.isdir(output_url):
            os.makedirs(output_url)

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
        instance["search_heuristic"] = ss # 1 dom_w_deg, 2 impact, 3 input_order
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
