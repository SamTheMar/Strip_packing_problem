import numpy as np
from z3 import *

from common.utils import PositionedRectangle, Rectangle
from SAT.SAT_solver import SAT_solver


class SAT_solver_rotated(SAT_solver):
    # def __init__(self, W, H, rectangles, break_symmetries = False, timeout = 300):
    #     super().__init__(W, H, rectangles, break_symmetries = break_symmetries, timeout = timeout)
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)


    def order_encode_variables(self):
        """
        Add also the rotation varaible R.
        R is true <=> the rectangle is rotated.
        R is false <=> the rectangle is not rotated.
        """
        super().order_encode_variables()
        self.R = [Bool(f"R_{i+1}") for i in range(self.n)]


    def add_3l_clause(self, direction, index_1, index_2):
        if direction == 'x':
            rectangle_measure = self.rectangles[index_1].w
            other_measure = self.rectangles[index_1].h
            strip_measure = self.W
            lrud = self._lr
            pxy = self._px
        elif direction == 'y':
            rectangle_measure = self.rectangles[index_1].h
            other_measure = self.rectangles[index_1].w
            strip_measure = self.H
            lrud = self._ud
            pxy = self._py
        else:
            print("The direction must be either 'x' or 'y'")
            return

        # do not allow rotation if rectangle height (width) is larger than strip width (height)
        if other_measure > strip_measure:
            self.s.add(Not(self.R[index_1]))

        # force rotation if rectangle width (height) is larger than strip width (height)
        if rectangle_measure > strip_measure:
            self.s.add(self.R[index_1])

        # if rectangle 1 is left of rectangle 2, rectangle 2 cannot be at the left of the right edge of rectangle 1.
        # no rotation
        for k in range(min(rectangle_measure, strip_measure)):
            self.s.add(Implies(Not(self.R[index_1]),
                                Or(Not(lrud[index_1][index_2]), Not(pxy[index_2][k]))))
        for k in range(strip_measure - rectangle_measure):
            k1 = k + rectangle_measure
            self.s.add(Implies(Not(self.R[index_1]),
                                Or(Not(lrud[index_1][index_2]), pxy[index_1][k], Not(pxy[index_2][k1]))))
        
        # rotation
        for k in range(min(other_measure, strip_measure)):
            self.s.add(Implies(self.R[index_1],
                                Or(Not(lrud[index_1][index_2]), Not(pxy[index_2][k]))))
        for k in range(strip_measure - other_measure):
            k1 = k + other_measure
            self.s.add(Implies(self.R[index_1],
                                Or(Not(lrud[index_1][index_2]), pxy[index_1][k], Not(pxy[index_2][k1]))))


    def domain_reducing_constraints(self):
        for i in range(self.n):
            # No rotation
            for e in range(self.W - self.rectangles[i].w, self.W):
                self.s.add(Implies(Not(self.R[i]), self._px[i][e]))
            for f in range(self.H - self.rectangles[i].h, self.H):
                self.s.add(Implies(Not(self.R[i]), self._py[i][f]))
            # rotation
            for e in range(self.W - self.rectangles[i].h, self.W):
                self.s.add(Implies(self.R[i], self._px[i][e]))
            for f in range(self.H - self.rectangles[i].w, self.H):
                self.s.add(Implies(self.R[i], self._py[i][f]))

        if self.break_symmetries:
            m = np.argmax([r.w * r.h for r in self.rectangles])
            # no rotation
            for e in range((self.W - self.rectangles[m].w) // 2, self.W - self.rectangles[m].w):
                self.s.add(Implies(Not(self.R[m]), self._px[m][e]))
            for f in range((self.H - self.rectangles[m].h) // 2, self.H - self.rectangles[m].h):
                self.s.add(Implies(Not(self.R[m]), self._py[m][f]))
            # rotation
            for e in range((self.W - self.rectangles[m].h) // 2, self.W - self.rectangles[m].h):
                self.s.add(Implies(self.R[m], self._px[m][e]))
            for f in range((self.H - self.rectangles[m].w) // 2, self.H - self.rectangles[m].w):
                self.s.add(Implies(self.R[m], self._py[m][f]))


    def ordering_constraints(self):
        for i in range(self.n):
            for e in range(self.W - 1):
                self.s.add(Implies(self._px[i][e], self._px[i][e + 1]))

            for f in range(self.H - 1):
                self.s.add(Implies(self._py[i][f], self._py[i][f + 1]))


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
        x_values = [self.order_decode(p) for p in px_eval]

        py_eval = [[m.evaluate(self._py[i][j], model_completion = True) for j in range(len(self._py[i]))] for i in range(len(self._py))]
        y_values = [self.order_decode(p) for p in py_eval]

        true_rectangles = []
        for rect, rot in zip(self.rectangles, self.R):
            if m.evaluate(rot, model_completion = True):
                true_rectangles.append(Rectangle(rect.h, rect.w))
            else:
                true_rectangles.append(rect)

        return [PositionedRectangle(x, y, rect.w, rect.h) for x, y, rect in zip(x_values, y_values, true_rectangles)]
