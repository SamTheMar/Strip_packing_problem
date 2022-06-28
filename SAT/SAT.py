from turtle import position
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

def max_area(rectangles):
    ind_max = 0
    area_max = rectangles[0].w * rectangles[0].h
    for i in range(len(rectangles)):
        if rectangles[i].w > area_max:
            ind_max = i
            area_max = rectangles[i].w * rectangles[i].h

    return ind_max

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


def order_encode_variables(W, H, rectangles):
    n = len(rectangles)
    px = [[Bool(f"px_{i+1}_{e}") for e in range(W - rectangles[i].w)] for i in range(n)]
    py = [[Bool(f"py_{i+1}_{f}") for f in range(H - rectangles[i].h)] for i in range(n)]

    lr = [[Bool(f"lr_{i+1}_{j+1}") for j in range(n)] for i in range(n)]
    ud = [[Bool(f"ud_{i+1}_{j+1}") for j in range(n)] for i in range(n)]

    return px, py, lr, ud


def valid_problem(W, H, rectangles):
    for i in range(len(rectangles)):
        if rectangles[i].w > W:
            print("Invalid: there is a rectangle that is wider than the strip!")
            return False
    
        if rectangles[i].h > H:
            print("Invalid: there is a rectangle that is taller than the strip!")
            return False
    return True


def ordering_constraints(s, rectangles, px, py):
    n = len(rectangles)
    for i in range(n):
        for e in range(len(px[i]) - 1):
            s.add(Implies(px[i][e], px[i][e + 1]))

        for f in range(len(py[i]) - 1):
            s.add(Implies(py[i][f], py[i][f + 1]))


def non_overlapping_4l_constraints(s, rectangles, W, H, lr, ud):
    for i in range(len(rectangles)):
        for j in range(i):
            to_add = []
            if rectangles[i].w + rectangles[j].w <= W:
                to_add += [lr[i][j], lr[j][i]]
            if rectangles[i].h + rectangles[j].h <= H:
                to_add += [ud[i][j], ud[j][i]]

            s.add(Or(to_add))


def non_overlapping_4l_constraints_SB(s, rectangles, W, H, lr, ud):
    m = max_area(rectangles)

    ind_max1, ind_max2 = two_largest_index(rectangles)

    for i in range(len(rectangles)):
        for j in range(i):
            to_add = []

            # Reducing the possibilities for placing large rectangles(LR)
            if rectangles[i].w + rectangles[j].w <= W:
                # Breaking symmetries for same-sized rectangles(SR)
                if rectangles[i].w == rectangles[j].w and rectangles[i].h == rectangles[j].h:
                    to_add += [lr[i][j]]
                # FIXME: LS symmetries braking don't work
                # Reducing the domain for the largest rectangle(LS)
                elif j == m:
                    to_add += [lr[j][i]]
                # Breaking symmetries for the largest pair of rectangles(LP)
                # elif i==ind_max1 and j==ind_max2:
                #     to_add += [lr[i][j]]
                # (LR)
                else:
                    to_add += [lr[i][j], lr[j][i]]
            # (LR)
            if rectangles[i].h + rectangles[j].h <= H:
                to_add += [ud[i][j], ud[j][i]]

            s.add(Or(to_add))


def non_overlapping_3l_constraints(s, rectangles, W, H, lr, ud, px, py):
    n = len(rectangles)
    for i in range(n):
        for j in range(n):
            if i==j: continue

            # rectangle j cannot be at the left of the right edge of rectangle i
            for k in range(min(rectangles[i].w, len(px[j]))):
                s.add(Or(Not(lr[i][j]), Not(px[j][k])))

            if rectangles[i].w + rectangles[j].w <= W:
                for e in range(W):
                    e1 = e + rectangles[i].w

                    if e < len(px[i]) and e1 < len(px[j]):
                        s.add(Or(Not(lr[i][j]), px[i][e], Not(px[j][e1])))

                    if e < len(px[i]) and e1 >= len(px[j]):
                        s.add(Or(Not(lr[i][j]), px[i][e]))

                    if e >= len(px[i]) and e1 < len(px[j]):
                        s.add(Or(Not(lr[i][j]), Not(px[j][e1])))


            # rectangle j cannot be under of the top edge of rectangle i
            for k in range(min(rectangles[i].h, len(py[j]))):
                s.add(Or(Not(ud[i][j]), Not(py[j][k])))

            if rectangles[i].h + rectangles[j].h <= H:
                for f in range(H):
                    f1 = f + rectangles[i].h

                    if f < len(py[i]) and f1 < len(py[j]):
                        s.add(Or(Not(ud[i][j]), py[i][f], Not(py[j][f1])))

                    if f < len(py[i]) and f1 >= len(py[j]):
                        s.add(Or(Not(ud[i][j]), py[i][f]))

                    if f >= len(py[i]) and f1 < len(py[j]):
                        s.add(Or(Not(ud[i][j]), Not(py[j][f1])))


def non_overlapping_3l_constraints_SB(s, rectangles, W, H, lr, ud, px, py):
    n = len(rectangles)
    m = max_area(rectangles)

    for i in range(n):
        for j in range(n):
            if i == j:
                continue

            # rectangle j cannot be at the left of the right edge of rectangle i
            for k in range(min(rectangles[i].w, len(px[j]))):
                s.add(Or(Not(lr[i][j]), Not(px[j][k])))

            # Reducing the possibilities for placing large rectangles(LR)
            if rectangles[i].w + rectangles[j].w <= W:
                # Breaking symmetries for same-sized rectangles(SR)
                if j > i and rectangles[i].w == rectangles[j].w and rectangles[i].h == rectangles[j].h:
                    s.add(Or(Not(ud[j][i]), Not(lr[i][j])))
                # FIXME: LS symmetries braking don't work
                # Reducing the domain for the largest rectangle(LS)
                elif i > j and j == m:
                    pass
                # (LR)
                else:
                    for e in range(W):
                        e1 = e + rectangles[i].w

                        if e < len(px[i]) and e1 < len(px[j]):
                            s.add(Or(Not(lr[i][j]), px[i][e], Not(px[j][e1])))

                        if e < len(px[i]) and e1 >= len(px[j]):
                            s.add(Or(Not(lr[i][j]), px[i][e]))

                        if e >= len(px[i]) and e1 < len(px[j]):
                            s.add(Or(Not(lr[i][j]), Not(px[j][e1])))

            # rectangle j cannot be under of the top edge of rectangle i
            for k in range(min(rectangles[i].h, len(py[j]))):
                s.add(Or(Not(ud[i][j]), Not(py[j][k])))

            if rectangles[i].h + rectangles[j].h <= H:
                for f in range(H):
                    f1 = f + rectangles[i].h

                    if f < len(py[i]) and f1 < len(py[j]):
                        s.add(Or(Not(ud[i][j]), py[i][f], Not(py[j][f1])))

                    if f < len(py[i]) and f1 >= len(py[j]):
                        s.add(Or(Not(ud[i][j]), py[i][f]))

                    if f >= len(py[i]) and f1 < len(py[j]):
                        s.add(Or(Not(ud[i][j]), Not(py[j][f1])))


def non_overlapping_constraints(s, rectangles, W, H, lr, ud, px, py, sb=False):
    if sb:
        non_overlapping_4l_constraints_SB(s, rectangles, W, H, lr, ud)
        non_overlapping_3l_constraints_SB(s, rectangles, W, H, lr, ud, px, py)
    else:
        non_overlapping_4l_constraints(s, rectangles, W, H, lr, ud)
        non_overlapping_3l_constraints(s, rectangles, W, H, lr, ud, px, py)



def SAT_solve(W, H, rectangles):
    """
    Find out if a strip of given width and height is satisfiable using SAT order encoding.

    Parameters
    ----------
    W : int
        total width of the strip
    H : int
        total height of the strip
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.

    Returns
    -------
    positioned_rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
        If the problem is UNSAT this list is empty.
    """
    px, py, lr, ud = order_encode_variables(W, H, rectangles)
    s = Solver()

    if not valid_problem(W, H, rectangles):
        return []

    ordering_constraints(s, rectangles, px, py)
    non_overlapping_constraints(s, rectangles, W, H, lr, ud, px, py, sb=True)

    s.set('timeout', 300 * 1000) ## seconds * milliseconds

    if s.check() == unsat:
        return []

    return decode_solver(s, rectangles, px, py)


def bisection_solve(W, H_lb, H_ub, rectangles, verbose=True):
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

        positioned_rectangles = SAT_solve(W, H, rectangles)
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


def SAT_optimize(W, rectangles, verbose=True):
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

    positioned_rectangles = SAT_solve(W, H_lb, rectangles)
    if len(positioned_rectangles) > 0:
        if verbose: print(f"Lower bound is SAT.\nOptimal value: H = {H_lb}.")
        return H_lb, positioned_rectangles

    if verbose:
        print("Lower bound is UNSAT.")
    return bisection_solve(W, H_lb+1, H_ub, rectangles, verbose)
