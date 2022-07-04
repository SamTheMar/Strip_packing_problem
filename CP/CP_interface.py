from datetime import timedelta
from minizinc import Instance, Model, Solver
from time import time

import sys
sys.path.append("./")
from common.utils import write_execution_time


timeout = timedelta(seconds=300) #300

rotation = False

if rotation:
    model_url = "./CP/VLSI-Rotation.mzn"
else:
    model_url = "./CP/VLSI.mzn"

model = Model(model_url) # modify search and restart strategy in the model file
solver = Solver.lookup("chuffed")

time_tables = []

for instance_num in range(1,41):
    input_url = "./CP/CP_instances/ins-%d.dzn"%instance_num
    if rotation:
        output_url = "./CP/CP_solutions_rotation/ins-%d-sol.txt"%instance_num
    else:
        output_url = "./CP/CP_solutions/ins-%d-sol.txt"%instance_num

    instance = Instance(solver, model)
    instance.add_file(input_url)

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

print(time_tables)
