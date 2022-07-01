import numpy as np

from SAT_solver import SAT_solver
from SAT_solver_rotated import SAT_solver_rotated

def bisection_solve(W, H_lb, H_ub, rectangles, break_symmetries = True, allow_rotation = False, verbose=True):
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
    break_symmetries : bool, default True
        Toggle whether using symmetry breaking. For the explanation of the broken symmetries, see docs of SAT_solve.
    allow_rotation : bool, default False
        Toggle whether to allow 90 degree rotation of the rectangles.
    verbose : bool, default True

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
            solver = SAT_solver_rotated(W, H, rectangles, break_symmetries)
        else:
            solver = SAT_solver(W, H, rectangles, break_symmetries)
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


def SAT_optimize(W, rectangles, break_symmetries = True, allow_rotation = False, verbose=True):
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
    break_symmetries : bool, default True
        Toggle whether using symmetry breaking. For the explanation of the broken symmetries, see docs of SAT_solve.
    allow_rotation : bool, default False
        Toggle whether to allow 90 degree rotation of the rectangles.
    verbose : bool, default True

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
        solver = SAT_solver_rotated(W, H_lb, rectangles, break_symmetries)
    else:
        if verbose:
            print("Rotation not allowed.")
        solver = SAT_solver(W, H_lb, rectangles, break_symmetries)
    positioned_rectangles = solver.solve()

    if len(positioned_rectangles) > 0:
        if verbose: print(f"Lower bound is SAT.\nOptimal value: H = {H_lb}.")
        return H_lb, positioned_rectangles

    if verbose:
        print("Lower bound is UNSAT.")
    return bisection_solve(W, H_lb+1, H_ub, rectangles, break_symmetries, verbose)


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


