import matplotlib.pyplot as plt
import numpy as np

import time
from z3 import Z3Exception
from subprocess import TimeoutExpired

from utils import visualize, read_instance, save_solution, sort_by_area

import sys
sys.path.append('../SAT')
sys.path.append('../SMT')
from SMT_Lib_utils import SMT_optimize
from SAT_utils import SAT_optimize


def compute_all_instances(mode = "SAT",
                            input_range=range(40),
                            plot=True,
                            save_to_file=True,
                            verbose=True,
                            allow_rotation=False,
                            sorting_by_area=True,
                            break_symmetries=True,
                            solver='z3',
                            logic='LIA',
                            timeout=300,
                            plot_kw={},
                            plot_output_format = 'png'):
    """
    Compute all instances using either a SAT or an SMT solver.

    Parameters
    ----------
    mode : string
        either SAT or SMT.
    ...todo

    """
    if mode != 'SAT' and mode != 'SMT':
        print("ERROR! The mode must either be SAT or SMT!")
        return

    input_folder = "../instances/"
    output_folder = f"../{mode}/out/"

    if allow_rotation:
        output_folder += "rotation/"
    else:
        output_folder += "no_rotation/"

    if sorting_by_area:
        output_folder += "sorting_by_area/"
    else:
        output_folder += "no_sorting_by_area/"

    plot_folder = output_folder + "plot/"
    output_folder += "txt/"

    print("")
    print(50*"=")
    for i in input_range:
        ins_filename = input_folder + f"ins-{i+1}.txt"
        solution_filename = output_folder + f"ins-{i+1}-sol.txt"
        W, n, rectangles = read_instance(ins_filename)

        if sorting_by_area:
            rectangles = sort_by_area(rectangles)

        m = np.argmax([r.w * r.h for r in rectangles])
        print(f"\nInstance {i+1}")
        print("Width:", W)
        print("Number of rectangles:", len(rectangles))
        print("Largest rectangle measures:",
              (rectangles[m].w, rectangles[m].h))
        print("Largest rectangle index:", m+1)
        print("Breaking symmetries:", break_symmetries)
        print("")

        execution_time = 0.
        H = 0
        try:
            start = time.time()
            if mode == "SAT":
                H, positioned_rectangles = SAT_optimize(W, rectangles, allow_rotation, verbose, break_symmetries, timeout=timeout)
            else:
                H, positioned_rectangles = SMT_optimize(W, rectangles, allow_rotation, verbose, break_symmetries, solver=solver, logic=logic, timeout=timeout)
            execution_time = time.time() - start
            print("\nFound height:", H)
            print(f"Execution time in seconds: {execution_time:.3f}")

            fig, ax = visualize(W, H, positioned_rectangles, **plot_kw)
            fig.suptitle(f"{ins_filename.split('/')[-1].split('.')[0]}, {n} rectangles, W = {W}, H = {H}")
            fig.tight_layout(pad=1)

            if save_to_file:
                plt.savefig(plot_folder + ins_filename.split('/')[-1].split('.')[0] + "." + plot_output_format.split('.')[-1])
                save_solution(solution_filename, W, H, positioned_rectangles)
                with open(solution_filename, "a") as f:
                    f.write(f"\nexecution time in seconds: {execution_time:.3f}")

            if plot:
                plt.show()
            else:
                plt.close(fig)

        except TimeoutExpired:
            print("\n----Timeout----\n")
        except Z3Exception:
            print("\n----Timeout----\n")
        print("")
        print(50*"=")
