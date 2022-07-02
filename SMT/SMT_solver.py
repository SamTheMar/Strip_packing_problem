import numpy as np
from z3 import *

import sys
sys.path.append("../common")
from utils import PositionedRectangle


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


    def domain(self):
        self.s.add([self._px[i] >= 0 for i in range(self.n)])
        self.s.add([self._py[i] >= 0 for i in range(self.n)])
        self.s.add([self._px[i] + self.rect_w[i] <=
                    self.W for i in range(self.n)])
        self.s.add([self._py[i] + self.rect_h[i] <=
                    self.H for i in range(self.n)])


    def add_constraints(self):
        for j in range(self.n):
            for i in range(j):
                self.s.add(Or(self._px[i] + self.rect_w[i] <= self._px[j],
                              self._px[j] + self.rect_w[j] <= self._px[i],
                              self._py[i] + self.rect_h[i] <= self._py[j],
                              self._py[j] + self.rect_h[j] <= self._py[i]))


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

        x_values = [m.evaluate(self._px[i], model_completion=True)
                    for i in range(len(self._px))]
        y_values = [m.evaluate(self._py[i], model_completion=True)
                    for i in range(len(self._py))]

        return [PositionedRectangle(x.as_long(), y.as_long(), rect.w, rect.h) for x, y, rect in zip(x_values, y_values, self.rectangles)]


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

        self.domain()
        self.add_constraints()

        z = self.s.minimize(self.H)

        if self.s.check() == unsat or type(z.value()) == z3.z3.ArithRef:
            return 0, []

        return z.value().as_long(), self.decode_solver()
