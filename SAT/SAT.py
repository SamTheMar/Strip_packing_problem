from turtle import position
import numpy as np
from z3 import *

import sys
sys.path.append("../common")

from utils import PositionedRectangle
from SAT_utils import order_decode


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
    if s.check() == unsat:
        return []

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

    for i in range(n):
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
    s : z3.Solver
        if the problem is SAT, the solver has calculated the encoded solution
    """
    px, py, lr, ud = order_encode_variables(W, H, rectangles)
    s = Solver()

    if not valid_problem(W, H, rectangles):
        s.add(False)
        return s
    ordering_constraints(s, rectangles, px, py)
    non_overlapping_4l_constraints(s, rectangles, W, H, lr, ud)
    non_overlapping_3l_constraints(s, rectangles, W, H, lr, ud, px, py)
    return s


# TODO: test this
def bisection_solve(W, H_lb, H_ub, rectangles):
    """
    Find the optimal height of the strip packing problem using SAT order encoding.
    The optimization is done using the bisection method

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

    Returns
    -------
    H : int
        optimal height of the strip
    positioned_rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    while H_lb < H_ub:
        H = (H_lb + H_ub)//2
        s = SAT_solve(W, H, rectangles)
        if s.check() == sat:
            H_ub = H
        else:
            H_lb = H + 1

    positioned_rectangles = decode_solver(s)
    return H, positioned_rectangles


def SAT_optmize(W, rectangles):
    """
    Find the optimal height of the strip packing problem using SAT order encoding.

    Parameters
    ----------
    W : int
        total width of the strip
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.

    Returns
    -------
    H : int
        size of the height of the strip
    rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
        A list of rectangles. This contains bottom left x and y coordinate and
        the width and height of every rectangle.
    """
    total_area = sum([r.h*r.w for r in rectangles])
    H_ub = sum([r.h for r in rectangles])

    H_lb = int(np.ceil((total_area)/W))

    return bisection_solve(W, H_lb, H_ub, rectangles)
