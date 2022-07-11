import matplotlib.pyplot as plt
import numpy as np

import time
from z3 import Z3Exception
from subprocess import TimeoutExpired

import os

from common.utils import visualize, read_instance, save_solution, sort_by_area, write_execution_time

from SMT.src.SMT_Lib_solver import SMT_Lib_solver
from SMT.src.SMT_Lib_solver_rotated import SMT_Lib_solver_rotated
from SAT.src.SAT_solver import SAT_solver
from SAT.src.SAT_solver_rotated import SAT_solver_rotated


def bisection_solve(W, H_lb, H_ub, rectangles, allow_rotation=False, verbose=True, mode = 'SAT', *args, **kwargs):
    """
    Find the optimal height of the strip packing problem using SMT order encoding.
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
    mode : string, default SAT
        either SAT or SMT.
    *args, **kwargs
        all additional arguments are passed to the solver.

    Returns
    -------
    H : int
        optimal height of the strip
    positioned_rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    if mode != 'SAT' and mode != 'SMT':
        print("ERROR! The mode must either be SAT or SMT!")
        return
    i = 0  # counter for logging
    positioned_rectangles_lastSAT = []  # to keep track of the last SAT height

    if verbose:
        print("\nUsing bisection method:")
    while H_lb < H_ub:
        i += 1
        if verbose:
            print(f"\nCycle {i}: \n{H_lb} <= H <= {H_ub}.")

        H = (H_lb + H_ub)//2
        if verbose:
            print(f"Trying H = {H}.")

        if mode == "SAT":
            if allow_rotation:
                solver = SAT_solver_rotated(W, H_lb, rectangles, *args, **kwargs)
            else:
                solver = SAT_solver(W, H_lb, rectangles, *args, **kwargs)
        else:
            if allow_rotation:
                solver = SMT_Lib_solver_rotated(W, H_lb, rectangles, *args, **kwargs)
            else:
                solver = SMT_Lib_solver(W, H_lb, rectangles, *args, **kwargs)
        positioned_rectangles = solver.solve()

        if len(positioned_rectangles) > 0:
            positioned_rectangles_lastSAT = positioned_rectangles  # save this configuration
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


def optimize(W, rectangles, allow_rotation, verbose, mode = 'SAT', *args, **kwargs):
    """
    Find the optimal height of the strip packing problem using SMT order encoding.
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
    mode : string, default SAT
        either SAT or SMT.
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
    if mode != 'SAT' and mode != 'SMT':
        print("ERROR! The mode must either be SAT or SMT!")
        return
    total_area = sum([r.h*r.w for r in rectangles])
    H_ub = sum([r.h for r in rectangles]) // 2

    H_lb = int(np.ceil((total_area)/W))

    if verbose:
        print("Finding optimal strip height.")
        print("Initial estimation:")
        print(f"{H_lb} <= H <= {H_ub}.")
        print("\nTrying lower bound first.")

    if mode == "SAT":
        if verbose: print("Solving using SAT.")
        if allow_rotation:
            if verbose: print("Rotation allowed.")
            solver = SAT_solver_rotated(W, H_lb, rectangles, *args, **kwargs)
        else:
            if verbose: print("Rotation not allowed.")
            solver = SAT_solver(W, H_lb, rectangles, *args, **kwargs)
    else:
        if verbose: print("Solving using SMT.")
        if allow_rotation:
            if verbose: print("Rotation allowed.")
            solver = SMT_Lib_solver_rotated(W, H_lb, rectangles, *args, **kwargs)
        else:
            if verbose: print("Rotation not allowed.")
            solver = SMT_Lib_solver(W, H_lb, rectangles, *args, **kwargs)

    positioned_rectangles = solver.solve()
    if len(positioned_rectangles) > 0:
        if verbose: print(f"Lower bound is SAT.\nOptimal value: H = {H_lb}.")
        return H_lb, positioned_rectangles

    if verbose:
        print("Lower bound is UNSAT.")
    return bisection_solve(W, H_lb+1, H_ub, rectangles, allow_rotation, verbose, *args, **kwargs)


def compute_all_instances(mode = 'SAT',
                            input_range=range(40),
                            input_folder = "./instances/",
                            save_to_file=True,
                            output_folder = None,
                            show_plot=True,
                            save_plot=False,
                            plot_folder = None,
                            verbose=True,
                            allow_rotation=False,
                            break_symmetries=True,
                            sort_rectangles_by_area=True,
                            solver='z3',
                            logic='LIA',
                            timeout=300,
                            plot_kw={},
                            plot_output_format = 'png'):
    """
    Compute all instances using either a SAT or an SMT solver.

    Parameters
    ----------
    mode : string, default 'SAT'
        either SAT or SMT.
    input_range : range or list of int
        instances to compute.
    input_folder : string, default './instances/'
        folder from which the instance files are taken.
    save_to_file : bool, default True
        if True, save the computation results.
    output_folder : string, optional
        folder in which the results are saved. If not given, the results are saved in the following folder hierarchy:
            ./<mode>/out/(no_)rotation/(no_)symmetry_breaking/(no_)sorting_by_area/.
    show_plot : bool, default True
        if True, show the plots of the resulting configuration as images.
    save_plot : bool, default False
        if True, save the plot images. Only useful if save_to_file is True. This is independent from show_plot.
    plot_folder : string, optional
        folder in which to save the plot images. Only useful if save_plot is True.
        If not given, the results are saved in a folder called 'plot/' where the computation results are saved.
    verbose : bool, default True
    allow_rotation : bool, default False
        if True, allow rotation of the rectangles.
    break_symmetries : bool, default True
        if True, let the solver break symmetries.
    sort_rectangles_by_area : bool, default True
        if True, sort rectangles be area before passing them to the solver.
    solver : string, default 'z3'
        Underlying solver to use, only z3 and cvc5 are currently supported. Only used if mode = 'SMT'.
    logic : string, default 'LIA'
         Underlying SMT-LIB logic to use. Only used if mode = 'SMT'.
    timeout : int, default 300
        timeout of each computation in seconds.
    plot_kw : dict
        addidtional keywork arguments passed to ``visualize``
    plot_output_format : string, default 'png'
        Output figure format. Only used if save_to_file is True.
    """
    if mode != 'SAT' and mode != 'SMT':
        print("ERROR! The mode must either be SAT or SMT!")
        return

    if output_folder is None:
        output_folder = f"./{mode}/out/"

        if allow_rotation:
            output_folder += "rotation/"
        else:
            output_folder += "no_rotation/"

        if break_symmetries:
            output_folder += "symmetry_breaking/"
        else:
            output_folder += "no_symmetry_breaking/"

        if sort_rectangles_by_area:
            output_folder += "sorting_by_area/"
        else:
            output_folder += "no_sorting_by_area/"

    if plot_folder is None:
        plot_folder = output_folder + "plot/"

    if save_plot:
        if not os.path.isdir(plot_folder): os.makedirs(plot_folder)
    if not os.path.isdir(output_folder): os.makedirs(output_folder)

    print("")
    print(50*"=")
    for i in input_range:
        ins_filename = f"ins-{i+1}.txt"
        solution_filename = os.path.join(output_folder, f"ins-{i+1}-sol.txt")
        W, n, rectangles = read_instance(os.path.join(input_folder, ins_filename))

        if sort_rectangles_by_area:
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
                H, positioned_rectangles = optimize(W, rectangles, allow_rotation, verbose, mode, break_symmetries, timeout=timeout)
            else:
                H, positioned_rectangles = optimize(W, rectangles, allow_rotation, verbose, mode, break_symmetries, solver=solver, logic=logic, timeout=timeout)
            execution_time = time.time() - start
            print("\nFound height:", H)
            print(f"Execution time in seconds: {execution_time:.3f}")

            fig, ax = visualize(W, H, positioned_rectangles, **plot_kw)
            fig.suptitle(f"{ins_filename.split('.')[0]}, {n} rectangles, W = {W}, H = {H}")
            fig.tight_layout(pad=1)

            if save_to_file:
                if save_plot:
                    plt.savefig(plot_folder + ins_filename.split('.')[0] + "." + plot_output_format.split('.')[-1])
                save_solution(solution_filename, W, H, positioned_rectangles)
                write_execution_time(solution_filename, execution_time)
            if show_plot:
                plt.show()
            else:
                plt.close(fig)

        except TimeoutExpired:
            print("\n----Timeout----\n")
        except Z3Exception:
            print("\n----Timeout----\n")
        print("")
        print(50*"=")
