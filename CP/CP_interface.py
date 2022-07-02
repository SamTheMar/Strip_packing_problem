from datetime import timedelta
from minizinc import Instance, Model, Solver
from time import time

import sys

from sqlalchemy import false
sys.path.append('./common')
from utils import visualize_from_file
import matplotlib.pyplot as plt


timeout = timedelta(seconds=300) #300

model_url = "./CP/VLSI.mzn"

model = Model(model_url)



solvers = ["gecode","chuffed"]

'''
solver = Solver.lookup("chuffed")

instance = Instance(solver, model)
instance.add_file("./CP/CP_instances/ins-1.dzn")
instance["search_heuristic"] = 3
instance["restart_strategy"] = 1

result = instance.solve(timeout=timeout)
#flatTime = result.statistics['flatTime']
time = result.statistics['time']
# initTime = result.statistics['initTime']
#solveTime = result.statistics['solveTime']
#optTime = result.statistics['optTime']
totalTime = time
print(result)
'''

time_tables = []

for instance_num in range(1,41):
    input_url = "./CP/CP_instances/ins-%d.dzn"%instance_num
    output_url = "./CP/CP_solutions/ins-%d.txt"%instance_num
    solver = Solver.lookup("chuffed")

    

    instance = Instance(solver, model)
    instance.add_file(input_url)
    instance["search_heuristic"] = 3
    instance["restart_strategy"] = 1

    try:
        start_time = time()
        result = instance.solve(timeout=timeout)
        time_tables.append(time()-start_time)

        result_str = str(result)

        with open(output_url, "w") as f:
            f.write(str(result))

        print(instance_num,"solved")
    except:
        print(instance_num,"not solved")

print(time_tables)

'''
for instance_num in range(2,3):
    find_solution = False
    for str_solver in solvers:
        for search in range(1,4):
            for restart in range(1,4):
                input_url = "./CP/CP_instances/ins-%d.dzn"%instance_num
                output_url = "./CP/CP_solutions/ins-%d.txt"%instance_num
                solver = Solver.lookup(str_solver)

                

                instance = Instance(solver, model)
                instance.add_file(input_url)
                instance["search_heuristic"] = search
                instance["restart_strategy"] = restart

                print(str(str_solver),search,restart)
                try:
                    result = instance.solve(timeout=timeout)

                    #flatTime = result.statistics['flatTime']
                    time = result.statistics['time']
                    #initTime = result.statistics['initTime']
                    #solveTime = result.statistics['solveTime']
                    #optTime = result.statistics['optTime']
                    # totalTime = flatTime + time + initTime + solveTime + optTime
                    totalTime = time
                    result_str = str(result)
                    print(totalTime, '/n', result_str)

                    if not find_solution:
                        with open(output_url, "w") as f:
                            f.write(str(result))
                        find_solution=True
                except:
                    pass
'''


# giving datetime.timedelta(0) as the start value makes sum work on tds 
# average_timedelta = sum(timedeltas, datetime.timedelta(0)) / len(timedeltas)



# visualize_from_file(output_url, plot_width = 900)
# plt.show()