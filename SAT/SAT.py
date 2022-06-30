import numpy as np
from z3 import *

import sys
sys.path.append("../common")

from utils import PositionedRectangle
from SAT_utils import order_decode


class SAT_solver():
    def __init__(self, W, H, rectangles, break_symmetries = False, timeout_seconds = 300):
        self.W = W
        self.H = H
        self.rectangles = rectangles
        self.n = len(rectangles)
        self.break_symmetries = break_symmetries
        self.s = Solver()
        self.s.set('timeout', timeout_seconds * 1000) ## seconds * milliseconds


    def order_encode_variables(self):
        self._px = [[Bool(f"px_{i+1}_{e}") for e in range(self.W)] for i in range(self.n)]
        self._py = [[Bool(f"py_{i+1}_{f}") for f in range(self.H)] for i in range(self.n)]

        self._lr = [[Bool(f"lr_{i+1}_{j+1}") for j in range(self.n)] for i in range(self.n)]
        self._ud = [[Bool(f"ud_{i+1}_{j+1}") for j in range(self.n)] for i in range(self.n)]


    def add_3l_clause(self, direction, index_1, index_2):
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
        direction : string
            either 'x' or 'y'.
        index_1 : int
            index of the first rectangle.
        index_2 : int
            index of the second rectangle.
        """
        if direction == 'x':
            rectangle_measure = self.rectangles[index_1].w
            strip_measure = self.W
            lrud = self._lr
            pxy = self._px
        elif direction == 'y':
            rectangle_measure = self.rectangles[index_1].h
            strip_measure = self.H
            lrud = self._ud
            pxy = self._py
        else:
            print("The direction must be either 'x' or 'y'")
            return

        #if rectangle 1 is left of rectangle 2, rectangle 2 cannot be at the left of the right edge of rectangle 1.
        for k in range(rectangle_measure):
            self.s.add(Or(Not(lrud[index_1][index_2]), Not(pxy[index_2][k])))

        for k in range(strip_measure - rectangle_measure):
            k1 = k + rectangle_measure
            self.s.add(Or(Not(lrud[index_1][index_2]), pxy[index_1][k], Not(pxy[index_2][k1])))


    def domain_reducing_constraints(self):
        for i in range(self.n):
            for e in range(self.W - self.rectangles[i].w, self.W):
                self.s.add(self._px[i][e])
            for e in range(self.H - self.rectangles[i].h, self.H):
                self.s.add(self._py[i][e])

        if self.break_symmetries:
            m = np.argmax([r.w * r.h for r in self.rectangles])
            for e in range((self.W - self.rectangles[m].w) // 2, self.W - self.rectangles[m].w):
                self.s.add(self._px[m][e])
            for f in range((self.H - self.rectangles[m].h) // 2, self.H - self.rectangles[m].h):
                self.s.add(self._py[m][f])


    def ordering_constraints(self):
        for i in range(self.n):
            for e in range(self.W - self.rectangles[i].w - 1):
                self.s.add(Implies(self._px[i][e], self._px[i][e + 1]))

            for f in range(self.H - self.rectangles[i].h - 1):
                self.s.add(Implies(self._py[i][f], self._py[i][f + 1]))


    def add_non_overlapping_constraint(self, i, j, to_add = [True, True, True, True]):
        literals_4l = []
        if to_add[0]:
            literals_4l.append(self._lr[i][j])
            self.add_3l_clause('x', i, j)
        if to_add[1]:
            literals_4l.append(self._lr[j][i])
            self.add_3l_clause('x', j, i)
        if to_add[2]:
            literals_4l.append(self._ud[i][j])
            self.add_3l_clause('y', i, j)
        if to_add[3]:
            literals_4l.append(self._ud[j][i])
            self.add_3l_clause('y', j, i)

        self.s.add(Or(literals_4l))


    def non_overlapping_constraints(self):
        for j in range(self.n):
            for i in range(j):
                self.add_non_overlapping_constraint(i, j)


    def non_overlapping_constraints_SB(self):
        m = np.argmax([r.w * r.h for r in self.rectangles]) # index of rectangle with max area

        for j in range(self.n):
            for i in range(j):
                # LS: Reducing the domain for the largest rectangle
                if j == m:
                    large_width = self.rectangles[i].w > (self.W - self.rectangles[m].w)//2
                    large_height = self.rectangles[i].h > (self.H - self.rectangles[m].h)//2
                    if large_width and large_height:
                        self.add_non_overlapping_constraint(i, j, [False, True, False, True])
                    elif large_width:
                        self.add_non_overlapping_constraint(i, j, [False, True, True, True])
                    elif large_height:
                        self.add_non_overlapping_constraint(i, j, [True, True, False, True])
                    else:
                        self.add_non_overlapping_constraint(i, j)
                # SR: Breaking symmetries for same-sized rectangles
                elif self.rectangles[i].w == self.rectangles[j].w and self.rectangles[i].h == self.rectangles[j].h:
                    self.add_non_overlapping_constraint(i, j, [True, False, True, True])
                    self.s.add(Or(Not(self._ud[i][j], self._lr[j][i])))
                # LR (horizontal)
                elif self.rectangles[i].w + self.rectangles[j].w > self.W:
                    self.add_non_overlapping_constraint(i, j, [False, False, True, True])
                # LR (vertical)
                elif self.rectangles[i].h + self.rectangles[j].h > self.H:
                    self.add_non_overlapping_constraint(i, j, [True, True, False, False])
                else:
                    self.add_non_overlapping_constraint(i, j)


    def decode_solver(self):
        """
        Decode the variables of the ground solver.

        Returns
        -------
        positioned_rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
            A list of rectangles. This contains bottom left x and y coordinate and
            the width and height of every rectangle.
        """
        m = self.s.model()

        px_eval = [[m.evaluate(self._px[i][j], model_completion = True) for j in range(len(self._px[i]))] for i in range(len(self._px))]
        x_values = [order_decode(p) for p in px_eval]

        py_eval = [[m.evaluate(self._py[i][j], model_completion = True) for j in range(len(self._py[i]))] for i in range(len(self._py))]
        y_values = [order_decode(p) for p in py_eval]

        return [PositionedRectangle(x, y, rect.w, rect.h) for x, y, rect in zip(x_values, y_values, self.rectangles)]


    def solve(self):
        """
        Find out if a strip of given width and height is satisfiable using SAT order encoding.
        By default, symmetry breaking is used. The broken symmetries are:
        - LR: Reducing the possibilities for placing large rectangles
        - SR: Breaking symmetries for same-sized rectangles
        - LS: Reducing the domain for the largest rectangle

        Returns
        -------
        positioned_rectangles : list of namedtuple('PositionedRectangle', ['x', 'y', 'w', 'h'])
            A list of rectangles. This contains bottom left x and y coordinate and
            the width and height of every rectangle.
            If the problem is UNSAT this list is empty.
        """
        self.order_encode_variables()

        self.domain_reducing_constraints()
        self.ordering_constraints()

        if self.break_symmetries:
            self.non_overlapping_constraints_SB()
        else:
            self.non_overlapping_constraints()

        if self.s.check() == unsat:
            return []

        return self.decode_solver()


def two_largest_index(rectangles):
    area = [r.w * r.h for r in rectangles]
    sorted_area = sorted(area)
    largest = sorted_area[-1]
    second_largest = sorted_area[-2]
    return area.index(largest), area.index(second_largest)


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

        positioned_rectangles = SAT_solver(W, H, rectangles, break_symmetries).solve()
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

    positioned_rectangles = SAT_solver(W, H_lb, rectangles, break_symmetries).solve()
    if len(positioned_rectangles) > 0:
        if verbose: print(f"Lower bound is SAT.\nOptimal value: H = {H_lb}.")
        return H_lb, positioned_rectangles

    if verbose:
        print("Lower bound is UNSAT.")
    return bisection_solve(W, H_lb+1, H_ub, rectangles, break_symmetries, verbose)
