import numpy as np
import time
import matplotlib.pyplot as plt

from z3 import Z3Exception
from SAT_solver import SAT_solver
from SAT_solver_rotated import SAT_solver_rotated

import sys
sys.path.append("../common")
from utils import sort_by_area, read_instance, visualize, read_instance, save_solution


def bisection_solve(W, H_lb, H_ub, rectangles, allow_rotation = False, verbose=True, *args, **kwargs):
    """
    Find the optimal height of the strip packing problem using SAT order encoding.
    The optimization is done using the bisection method.

    Parameters
    ----------
    W : int
        total width of the strip
    H_lb : int
        lower bound for the height of the strip
    H_ub : int
        upper bound for the height of the strip
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.
    allow_rotation : bool, default False
        Toggle whether to allow 90 degree rotation of the rectangles.
    verbose : bool, default True
    *args, **kwargs
        all additional arguments are passed to the solver

    Returns
    -------
    H : int
        optimal height of the strip
    positioned_rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    i = 0 # counter for logging
    positioned_rectangles_lastSAT = [] #to keep track of the last SAT height

    if verbose: print("\nUsing bisection method:")
    while H_lb < H_ub:
        i += 1
        if verbose: print(f"\nCycle {i}: \n{H_lb} <= H <= {H_ub}.")

        H = (H_lb + H_ub)//2
        if verbose: print(f"Trying H = {H}.")

        if allow_rotation:
            solver = SAT_solver_rotated(W, H, rectangles, *args, **kwargs)
        else:
            solver = SAT_solver(W, H, rectangles, *args, **kwargs)
        positioned_rectangles = solver.solve()

        if len(positioned_rectangles) > 0:
            positioned_rectangles_lastSAT = positioned_rectangles #save this configuration
            H_ub = H
            if verbose:
                print(f"SAT.")
        else:
            H_lb = H + 1
            if verbose:
                print(f"UNSAT.")

    # if the last height is UNSAT, use the configuration used for the previous height
    if H_lb > H:
        positioned_rectangles = positioned_rectangles_lastSAT

    if verbose:
        print(f"\nOptimal value: H = {H_lb}.")
    return H_lb, positioned_rectangles


def SAT_optimize(W, rectangles, allow_rotation = False, verbose=True, *args, **kwargs):
    """
    Find the optimal height of the strip packing problem using SAT order encoding.
    The bisection method is used to optimize the strip height.

    The lower bound for the strip height is given by: ceil(total_area/strip_width),
    The upper bound is the sum of the heights of the rectangles.

    The lower bound for the height is tried first before the bisection method.

    Parameters
    ----------
    W : int
        total width of the strip
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.
    allow_rotation : bool, default False
        Toggle whether to allow 90 degree rotation of the rectangles.
    verbose : bool, default True
    *args, **kwargs
        all additional arguments are passed to the solver.

    Returns
    -------
    H : int
        optimal height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    total_area = sum([r.h*r.w for r in rectangles])
    H_ub = sum([r.h for r in rectangles]) // 2

    H_lb = int(np.ceil((total_area)/W))

    if verbose:
        print("Finding optimal strip height.")
        print("Initial estimation:")
        print(f"{H_lb} <= H <= {H_ub}.")
        print("\nTrying lower bound first.")

    if allow_rotation:
        if verbose:
            print("Rotation allowed.")
        solver = SAT_solver_rotated(W, H_lb, rectangles, *args, **kwargs)
    else:
        if verbose:
            print("Rotation not allowed.")
        solver = SAT_solver(W, H_lb, rectangles, *args, **kwargs)
    positioned_rectangles = solver.solve()

    if len(positioned_rectangles) > 0:
        if verbose: print(f"Lower bound is SAT.\nOptimal value: H = {H_lb}.")
        return H_lb, positioned_rectangles

    if verbose:
        print("Lower bound is UNSAT.")
    return bisection_solve(W, H_lb+1, H_ub, rectangles, allow_rotation, verbose *args, **kwargs)


def order_encode(value, vmin=0, vmax=-1):
    """
    Parameters
    ----------
    value : int
        value to encode
    vmin : int, defualt 0
        starting value of the domain
    vmax : int, optional
        final value of the domain. Defaults to value

    Returns
    -------
    list of bool
        the order encoded value in the form [False, ..., False, True, True, ...]
    """
    if vmax < value:
        if vmax != -1:
            print(
                "Attention! The given length of the encoding is smaller than the value to encode!")
        vmax = value

    if value < vmin:
        print(
            "Attention! The encoded value is smaller than the minimum value of the domain!")

    encoding = []
    for i in range(vmin, vmax):
        encoding.append(value <= i)
    return encoding


def compute_all_instances_SAT(input_range=range(40), plot=True, save_to_file=True, verbose=True, allow_rotation=False, sorting_by_area=True, break_symmetries=True, timeout=300, plot_kw={}):

    input_folder = "../instances/"
    output_folder = f"out/"

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
        print("Largest rectangle measures:", (rectangles[m].w, rectangles[m].h))
        print("Largest rectangle index:", m+1)
        print("Breaking symmetries:", break_symmetries)
        print("")

        execution_time = 0.
        H = 0
        try:
            start = time.time()
            H, positioned_rectangles = SAT_optimize(W, rectangles, allow_rotation, verbose, break_symmetries, timeout=timeout)
            execution_time = time.time() - start
            print("\nFound height:", H)
            print(f"Execution time in seconds: {execution_time:.3f}")

            if save_to_file:
                save_solution(solution_filename, W, H, positioned_rectangles)
                with open(solution_filename, "a") as f:
                    f.write(f"\nexecution time in seconds: {execution_time:.3f}")
            if plot:
                fig, ax = visualize(W, H, positioned_rectangles, **plot_kw)
                fig.suptitle(
                    f"{ins_filename.split('/')[-1].split('.')[0]}, {n} rectangles, W = {W}, H = {H}")
                fig.tight_layout(pad=1)
                if save_to_file:
                    plt.savefig(plot_folder + ins_filename.split('/')[-1].split('.')[0])
                plt.show()

        except Z3Exception:
            print("\n----Timeout----\n")

        print("")
        print(50*"=")
