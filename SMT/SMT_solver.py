import numpy as np
from z3 import *

from common.utils import PositionedRectangle


class SMT_solver():
    def __init__(self, W, rectangles, break_symmetries=False, timeout_seconds=300):
        self.W = W
        self.rectangles = rectangles
        self.n = len(rectangles)
        self.break_symmetries = break_symmetries
        self.s = Optimize()
        self.s.set('timeout', timeout_seconds * 1000)  # seconds * milliseconds


    def order_encode_variables(self):
        self._px = [Int(f"px_{i+1}") for i in range(self.n)]
        self._py = [Int(f"py_{i+1}") for i in range(self.n)]

        self.rect_w = [IntVal(int(rect.w)) for rect in self.rectangles]
        self.rect_h = [IntVal(int(rect.h)) for rect in self.rectangles]

        self.H = Int('H')


    def domain_constraints(self):
        self.s.add([self._px[i] >= 0 for i in range(self.n)])
        self.s.add([self._py[i] >= 0 for i in range(self.n)])

        self.s.add([self._py[i] + self.rect_h[i] <= self.H for i in range(self.n)])
        # LS: Reducing the domain for the largest rectangle
        if self.break_symmetries:
            m = np.argmax([r.w * r.h for r in self.rectangles])
            self.s.add([self._px[i] + self.rect_w[i] <= self.W for i in range(self.n) if i!=m])
            self.s.add(self._px[m] + self.rect_w[m] <= self.W//2)
        else:
            self.s.add([self._px[i] + self.rect_w[i] <= self.W for i in range(self.n)])


    def add_non_overlapping_constraint(self, i, j, to_add = [True, True, True, True]):
        terms = []
        if to_add[0]:
            terms.append(self._px[i] + self.rect_w[i] <= self._px[j])
        if to_add[1]:
            terms.append(self._px[j] + self.rect_w[j] <= self._px[i])
        if to_add[2]:
            terms.append(self._py[i] + self.rect_h[i] <= self._py[j])
        if to_add[3]:
            terms.append(self._py[j] + self.rect_h[j] <= self._py[i])

        self.s.add(Or(terms))


    def non_overlapping_constraints(self):
        for j in range(self.n):
            for i in range(j):
                self.add_non_overlapping_constraint(i, j)


    def non_overlapping_constraints_SB(self):
        m = np.argmax([r.w * r.h for r in self.rectangles])
        for j in range(self.n):
            for i in range(j):
                if j == m and self.rectangles[i].w > (self.W - self.rectangles[m].w)//2:
                    self.add_non_overlapping_constraint(i, j, [False, True, True, True])
                # SR: Breaking symmetries for same-sized rectangles
                elif self.rectangles[i].w == self.rectangles[j].w and self.rectangles[i].h == self.rectangles[j].h:
                    self.add_non_overlapping_constraint(i, j, [True, False, True, True])
                # LR (horizontal): Reducing the possibilities for placing large rectangles
                elif self.rectangles[i].w + self.rectangles[j].w > self.W:
                    self.add_non_overlapping_constraint(i, j, [False, False, True, True])
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

        x_values = [m.evaluate(self._px[i], model_completion=True) for i in range(len(self._px))]
        y_values = [m.evaluate(self._py[i], model_completion=True) for i in range(len(self._py))]

        return [PositionedRectangle(x.as_long(), y.as_long(), rect.w, rect.h) for x, y, rect in zip(x_values, y_values, self.rectangles)]


    def solve(self):
        """
        Find out if a strip of given width and height is satisfiable using SMT.
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
        self.domain_constraints()

        if self.break_symmetries:
            self.non_overlapping_constraints_SB()
        else:
            self.non_overlapping_constraints()

        z = self.s.minimize(self.H)

        if self.s.check() == unsat or type(z.value()) == z3.z3.ArithRef:
            return 0, []

        return z.value().as_long(), self.decode_solver()
