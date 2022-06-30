import numpy as np
from z3 import *

import sys
sys.path.append("../common")

from utils import PositionedRectangle
from SAT_utils import order_decode


def two_largest_index(rectangles):
    area = [r.w * r.h for r in rectangles]
    sorted_area = sorted(area)
    largest = sorted_area[-1]
    second_largest = sorted_area[-2]
    return area.index(largest), area.index(second_largest)


def decode_solver(s, rectangles, px, py):
    """
    Decode the variables of the ground solver.

    Parameters
    ----------
    s : z3.Solver
        solver with a SAT interpretation of the problem.
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.
    px : list of bool
        encoded variables for the x-coordinates of the rectangles.
    py : list of bool
        encoded variables for the y-coordinates of the rectangles.

    Returns
    -------
    positioned_rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    m = s.model()

    px_eval = [[m.evaluate(px[i][j], model_completion = True) for j in range(len(px[i]))] for i in range(len(px))]
    x_values = [order_decode(p) for p in px_eval]

    py_eval = [[m.evaluate(py[i][j], model_completion = True) for j in range(len(py[i]))] for i in range(len(px))]
    y_values = [order_decode(p) for p in py_eval]

    return [PositionedRectangle(x, y, rect.w, rect.h) for x, y, rect in zip(x_values, y_values, rectangles)]


def valid_problem(W, H, rectangles):
    for i in range(len(rectangles)):
        if rectangles[i].w > W:
            print("Invalid: there is a rectangle that is wider than the strip!")
            return False
    
        if rectangles[i].h > H:
            print("Invalid: there is a rectangle that is taller than the strip!")
            return False
    return True


def order_encode_variables(s, W, H, rectangles):
    n = len(rectangles)
    px = [[Bool(f"px_{i+1}_{e}") for e in range(W)] for i in range(n)]
    py = [[Bool(f"py_{i+1}_{f}") for f in range(H)] for i in range(n)]

    lr = [[Bool(f"lr_{i+1}_{j+1}") for j in range(n)] for i in range(n)]
    ud = [[Bool(f"ud_{i+1}_{j+1}") for j in range(n)] for i in range(n)]

    return px, py, lr, ud


def add_clause_3l(s, rectangles, direction, strip_measure, index_1, index_2, relative_position_encoding, coordinate_encoding):
    """
    Add the normal 3-literal clause.
    I.e.
     - For the x-coordinate:
        ~lr[i][j] \/ px[i][e] \/ ~px[j][e + w_i].

     - For the y-coordinate:
        ~ud[i][j] \/ py[i][f] \/ ~py[j][f + h_i].

    Parameters
    ----------
    s : z3.Solver
        solver on which to add the clauses
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.
    direction : string
        either 'x' or 'y'.
    strip_measure : int
        size of the strip along the given direction.
    index_1 : int
        index of the first rectangle.
    index_2 : int
        index of the second rectangle.
    relative_position_encoding : list of z3.Bool
        encoding of the variable representing the relative position of rectangles i and j
        for the coordinate of interest.
        I.e. lr for the x-coordinate and ud for the y-coordinate.
    coordinate_encoding : list of z3.Bool
        order encoding of the coordinate.
        I.e. px for the x-coordinate and py for the y-coordinate.
    """
    if direction == 'x':
        rectangle_measure = rectangles[index_1].w
    elif direction == 'y':
        rectangle_measure = rectangles[index_1].h
    else:
        print("The direction must be either 'x' or 'y'")
        return

    cp = coordinate_encoding
    lrud = relative_position_encoding

    #if rectangle 1 is left of rectangle 2, rectangle 2 cannot be at the left of the right edge of rectangle 1.
    for k in range(rectangle_measure):
        s.add(Or(Not(lrud[index_1][index_2]), Not(cp[index_2][k])))

    for k in range(strip_measure - rectangle_measure):
        k1 = k + rectangle_measure
        s.add(Or(Not(lrud[index_1][index_2]), cp[index_1][k], Not(cp[index_2][k1])))


def domain_reducing_constraints(s, rectangles, W, H, px, py, break_symmetries):
    for i in range(len(rectangles)):
        for e in range(W - rectangles[i].w, W):
            s.add(px[i][e])
        for e in range(H - rectangles[i].h, H):
            s.add(py[i][e])

    if break_symmetries:
        m = np.argmax([r.w * r.h for r in rectangles])
        for e in range((W - rectangles[m].w) // 2, W - rectangles[m].w):
            s.add(px[m][e])
        for f in range((H - rectangles[m].h) // 2, H - rectangles[m].h):
            s.add(py[m][f])


def ordering_constraints(s, rectangles, px, py):
    W = len(px[0])
    H = len(py[0])
    n = len(rectangles)
    for i in range(n):
        for e in range(W - rectangles[i].w - 1):
            s.add(Implies(px[i][e], px[i][e + 1]))

        for f in range(H - rectangles[i].h - 1):
            s.add(Implies(py[i][f], py[i][f + 1]))


def add_normal_non_overlapping_constraint(s, rectangles, W, H, i, j, lr, ud, px, py):
    s.add(Or(lr[i][j], lr[j][i], ud[i][j], ud[j][i]))

    # 3l constraints
    add_clause_3l(s, rectangles, 'x', W, i, j, lr, px)
    add_clause_3l(s, rectangles, 'x', W, j, i, lr, px)

    add_clause_3l(s, rectangles, 'y', H, i, j, ud, py)
    add_clause_3l(s, rectangles, 'y', H, j, i, ud, py)


def non_overlapping_constraints(s, rectangles, W, H, lr, ud, px, py):
    for j in range(len(rectangles)):
        for i in range(j):
            add_normal_non_overlapping_constraint(s, rectangles, W, H, i, j, lr, ud, px, py)

#TODO: review symmetries
def non_overlapping_constraints_SB(s, rectangles, W, H, lr, ud, px, py):
    n = len(rectangles)
    m = np.argmax([r.w * r.h for r in rectangles]) # index of rectangle with max area
    
    #non_overlapping_constraints(s, rectangles, W, H, lr, ud, px, py)
    for j in range(n):
        for i in range(j):

            # LS: Reducing the domain for the largest rectangle
            if j == m:
                large_width = rectangles[i].w > (W - rectangles[m].w)//2
                large_height = rectangles[i].h > (H - rectangles[m].h)//2
                if large_width and large_height:
                    s.add(Or(lr[j][i], ud[j][i]))
                    # 3l constraints
                    add_clause_3l(s, rectangles, 'x', W, j, i, lr, px)

                    add_clause_3l(s, rectangles, 'y', H, j, i, ud, py)
                elif large_width:
                    s.add(Or(lr[j][i], ud[i][j], ud[j][i]))
                    # 3l constraints
                    add_clause_3l(s, rectangles, 'x', W, j, i, lr, px)

                    add_clause_3l(s, rectangles, 'y', H, i, j, ud, py)
                    add_clause_3l(s, rectangles, 'y', H, j, i, ud, py)
                elif large_height:
                    s.add(Or(lr[i][j], lr[j][i], ud[j][i]))
                    # 3l constraints
                    add_clause_3l(s, rectangles, 'x', W, i, j, lr, px)
                    add_clause_3l(s, rectangles, 'x', W, j, i, lr, px)

                    add_clause_3l(s, rectangles, 'y', H, j, i, ud, py)
                else:
                   add_normal_non_overlapping_constraint(s, rectangles, W, H, i, j, lr, ud, px, py)
            # SR: Breaking symmetries for same-sized rectangles
            elif rectangles[i].w == rectangles[j].w and rectangles[i].h == rectangles[j].h:
                s.add(Or(lr[i][j], ud[i][j], ud[j][i]))

                # 3l constraints
                add_clause_3l(s, rectangles, 'x', W, i, j, lr, px)

                add_clause_3l(s, rectangles, 'y', H, i, j, ud, py)
                add_clause_3l(s, rectangles, 'y', H, j, i, ud, py)
                s.add(Or(Not(ud[i][j], lr[j][i])))
            elif rectangles[i].w + rectangles[i].w > W:
                    s.add(Or(ud[i][j], ud[j][i]))
                    # 3l constraints
                    add_clause_3l(s, rectangles, 'y', H, i, j, ud, py)
                    add_clause_3l(s, rectangles, 'y', H, j, i, ud, py)
            elif rectangles[i].h + rectangles[i].h > H:
                    s.add(Or(lr[i][j], lr[j][i]))
                    # 3l constraints
                    add_clause_3l(s, rectangles, 'x', W, i, j, lr, px)
                    add_clause_3l(s, rectangles, 'x', W, j, i, lr, px)
            else:
                add_normal_non_overlapping_constraint(s, rectangles, W, H, i, j, lr, ud, px, py)


def SAT_solve(W, H, rectangles, break_symmetries = True):
    """
    Find out if a strip of given width and height is satisfiable using SAT order encoding.
    By default, symmetry breaking is used. The broken symmetries are:
     - LR: Reducing the possibilities for placing large rectangles
     - SR: Breaking symmetries for same-sized rectangles
     - LS: Reducing the domain for the largest rectangle

    Parameters
    ----------
    W : int
        total width of the strip
    H : int
        total height of the strip
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.
    break_symmetries : bool, default True
        Toggle whether using symmetry breaking

    Returns
    -------
    positioned_rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
        If the problem is UNSAT this list is empty.
    """
    s = Solver()
    px, py, lr, ud = order_encode_variables(s, W, H, rectangles)

    if not valid_problem(W, H, rectangles):
        return []

    domain_reducing_constraints(s, rectangles, W, H, px, py, break_symmetries)
    ordering_constraints(s, rectangles, px, py)

    print(f"non_overlapping_constraints: break_symmetries = {break_symmetries}")
    if break_symmetries:
        non_overlapping_constraints_SB(s, rectangles, W, H, lr, ud, px, py)
    else:
        non_overlapping_constraints(s, rectangles, W, H, lr, ud, px, py)

    s.set('timeout', 300 * 1000) ## seconds * milliseconds

    if s.check() == unsat:
        return []

    return decode_solver(s, rectangles, px, py)


def bisection_solve(W, H_lb, H_ub, rectangles, break_symmetries = True, verbose=True):
    """
    Find the optimal height of the strip packing problem using SAT order encoding.
    The optimization is done using the bisection method. The lower bound is tried first.

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

        positioned_rectangles = SAT_solve(W, H, rectangles, break_symmetries)
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


def SAT_optimize(W, rectangles, break_symmetries = True, verbose=True):
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

    positioned_rectangles = SAT_solve(W, H_lb, rectangles, break_symmetries)
    if len(positioned_rectangles) > 0:
        if verbose: print(f"Lower bound is SAT.\nOptimal value: H = {H_lb}.")
        return H_lb, positioned_rectangles

    if verbose:
        print("Lower bound is UNSAT.")
    return bisection_solve(W, H_lb+1, H_ub, rectangles, break_symmetries, verbose)
