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


#TODO: review symmetries
def order_encode_variables(W, H, rectangles, break_symmetries=True):
    n = len(rectangles)
    px = [[Bool(f"px_{i+1}_{e}") for e in range(W - rectangles[i].w)] for i in range(n)]
    py = [[Bool(f"py_{i+1}_{f}") for f in range(H - rectangles[i].h)] for i in range(n)]

    lr = [[Bool(f"lr_{i+1}_{j+1}") for j in range(n)] for i in range(n)]
    ud = [[Bool(f"ud_{i+1}_{j+1}") for j in range(n)] for i in range(n)]

    if break_symmetries:
        # LS: reduce domain of largest rectangle
        m = np.argmax([r.w * r.h for r in rectangles])
        px[m] = px[m][:len(px[m])//2]
        py[m] = px[m][:len(py[m])//2]

    return px, py, lr, ud


#TODO: review symmetries
def add_clause_4l(s, i, j, lr, ud, activation_list = [True, True, True, True]):
    to_add = []
    literal_list = [lr[i][j], lr[j][i], ud[i][j], ud[j][i]]
    for val, literal in zip(activation_list, literal_list):
        if val: to_add.append(literal)
    s.add(Or(to_add))


def add_false_before(s, rectangles, direction, index_1, index_2, relative_position_encoding, coordinate_encoding):
    """
    I.e. for the x-coordinate:
    rectangle j cannot be at the left of the right edge of rectangle i.
    Due to order encoding, the clause then looks like this:
     - i is left of j:
        lr[i][j] => forall k <= i: ~px[j][k].

    For the y-coordinate the clause is:
     - i is under of j
        ud[i][j] => forall k <= i: ~py[j][k].

    Parameters
    ----------
    s : z3.Solver
        solver on which to add the clauses
    rectangles : list of namedtuple('Rectangle', ['w', 'h'])
        A list of rectangles. This contains the width and height of every rectangle.
    direction : string
        either 'x' or 'y'.
    index_1 : int
        index of the first rectangle.
    index_2 : int
        index of the second rectangle.
    relative_position_encoding : list of z3.Bool
        encoding of the variable representing the relative position of rectangles i and j
        for the coordinate of interest.
        I.e. lr for the x-coordinate and ud for the y-coordinate.
    coordinate_encoding : list of z3.Bool
        order encoding of the coordinate. I.e. px for 
        I.e. px for the x-coordinate and py for the y-coordinate.
    """
    if direction == 'x':
        rectangle_measure = rectangles[index_1].w
    elif direction == 'y':
        rectangle_measure = rectangles[index_1].h
    else:
        print("The direction must be either 'x' or 'y'")
        return

    for k in range(min(rectangle_measure, len(coordinate_encoding[index_2]))):
        s.add(Or(Not(relative_position_encoding[index_1][index_2]), Not(coordinate_encoding[index_2][k])))


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

    # k stands for either e or f
    for k in range(strip_measure):
        k1 = k + rectangle_measure

        if k < len(cp[index_1]) and k1 < len(cp[index_2]):
            s.add(Or(Not(lrud[index_1][index_2]), cp[index_1][k], Not(cp[index_2][k1])))

        if k < len(cp[index_1]) and k1 >= len(cp[index_2]):
            s.add(Or(Not(lrud[index_1][index_2]), cp[index_1][k]))

        if k >= len(cp[index_1]) and k1 < len(cp[index_2]):
            s.add(Or(Not(lrud[index_1][index_2]), Not(cp[index_2][k1])))


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


def non_overlapping_3l_constraints(s, rectangles, W, H, lr, ud, px, py):
    n = len(rectangles)

    for i in range(n):
        for j in range(n):
            if i==j: continue
            add_false_before(s, rectangles, 'x', i, j, lr, px)
            add_false_before(s, rectangles, 'y', i, j, ud, py)

            add_clause_3l(s, rectangles, 'x', W, i, j, lr, px)
            add_clause_3l(s, rectangles, 'y', H, i, j, ud, py)


#TODO: review symmetries
def non_overlapping_constraints_SB(s, rectangles, W, H, lr, ud, px, py):
    n = len(rectangles)
    m = np.argmax([r.w * r.h for r in rectangles]) # index of rectangle with max area

    for i in range(n):
        for j in range(i):
            # 3l initialization
            # rectangle j cannot be at the left of the right edge of rectangle i
            add_false_before(s, rectangles, 'x', i, j, lr, px)
            add_false_before(s, rectangles, 'x', j, i, lr, px)

            # rectangle j cannot be under of the top edge of rectangle i
            add_false_before(s, rectangles, 'y', i, j, ud, py)
            add_false_before(s, rectangles, 'y', j, i, ud, py)

            # LS: Reducing the domain for the largest rectangle
            if j == m and rectangles[i].w > (W - rectangles[m].w)//2:
                    add_clause_4l(s, i, j, lr, ud, [False, True, True, True])

                    add_clause_3l(s, rectangles, 'x', W, m, i, lr, px)
                    add_clause_3l(s, rectangles, 'y', H, i, m, ud, py)
                    add_clause_3l(s, rectangles, 'y', H, m, i, ud, py)

            # SR: Breaking symmetries for same-sized rectangles
            elif rectangles[i].w == rectangles[j].w and rectangles[i].h == rectangles[j].h:
                add_clause_4l(s, i, j, lr, ud, [True, False, True, True])

                add_clause_3l(s, rectangles, 'x', W, i, j, lr, px)
                add_clause_3l(s, rectangles, 'y', H, i, j, ud, py)
                add_clause_3l(s, rectangles, 'y', H, j, i, ud, py)
                s.add(Or(Not(ud[i][j]), lr[j][i]))

            # LR: Reducing the possibilities for placing large rectangles
            elif rectangles[i].w + rectangles[j].w > W:
                add_clause_4l(s, i, j, lr, ud, [False, False, True, True])

                add_clause_3l(s, rectangles, 'y', H, i, j, ud, py)
                add_clause_3l(s, rectangles, 'y', H, j, i, ud, py)

            else:
                to_add_4l = []
                if rectangles[i].w + rectangles[j].w <= W:
                    to_add_4l += [lr[i][j], lr[j][i]]
                if rectangles[i].h + rectangles[j].h <= H:
                    to_add_4l += [ud[i][j], ud[j][i]]

                s.add(Or(to_add_4l))

                add_clause_3l(s, rectangles, 'x', W, i, j, lr, px)
                add_clause_3l(s, rectangles, 'x', W, j, i, lr, px)
                add_clause_3l(s, rectangles, 'y', H, i, j, ud, py)
                add_clause_3l(s, rectangles, 'y', H, j, i, ud, py)


def non_overlapping_constraints(s, rectangles, W, H, lr, ud, px, py, break_symmetries):
    print(f"non_overlapping_constraints: break_symmetries = {break_symmetries}")
    if break_symmetries:
        non_overlapping_constraints_SB(s, rectangles, W, H, lr, ud, px, py)
    else:
        non_overlapping_4l_constraints(s, rectangles, W, H, lr, ud)
        non_overlapping_3l_constraints(s, rectangles, W, H, lr, ud, px, py)


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
    px, py, lr, ud = order_encode_variables(W, H, rectangles, break_symmetries)
    s = Solver()

    if not valid_problem(W, H, rectangles):
        return []

    ordering_constraints(s, rectangles, px, py)
    non_overlapping_constraints(s, rectangles, W, H, lr, ud, px, py, break_symmetries)

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
