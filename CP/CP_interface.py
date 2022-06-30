from minizinc import Instance, Model, Solver

import sys
sys.path.append('./common')
from utils import visualize_from_file
import matplotlib.pyplot as plt

instance_num = 2
#input_url = "./CP_instances/ins-%d.dzn"%instance_num
#output_url = "./CP_solutions/ins-%d.txt"%instance_num
#model_url = "./VLSI.mzn"

input_url = "./CP/CP_instances/ins-%d.dzn"%instance_num
output_url = "./CP/CP_solutions/ins-%d.txt"%instance_num
model_url = "./CP/VLSI.mzn"

#solver
gecode = Solver.lookup("gecode")
model = Model(model_url)

instance = Instance(gecode, model)
instance.add_file(input_url)

result = instance.solve()

with open(output_url, "w") as f:
    f.write(str(result))
