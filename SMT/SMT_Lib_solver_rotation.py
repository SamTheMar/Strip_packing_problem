from utils import PositionedRectangle
import subprocess
import numpy as np
from SMT_Lib_solver import SMT_Lib_solver

import sys
sys.path.append("../common")


class SMT_Lib_solver_rotation(SMT_Lib_solver):
    def __init__(self, W, H, rectangles, break_symmetries=False, timeout=300, logic="LIA", solver="z3"):
        super().__init__(W, H, rectangles, break_symmetries, timeout, logic, solver)


    def decisional_variables(self):
        super().decisional_variables()
        #R[i] means that rectangle i is rotated
        for i in range(self.n):
            self.lines.append(f"(declare-fun R{i} () Bool)")


    def domain(self):
        self.lines += [f"(assert (>= posX{i} 0))" for i in range(self.n)]
        self.lines += [f"(assert (>= posY{i} 0))" for i in range(self.n)]

        if self.break_symmetries:
            m = np.argmax([r.w * r.h for r in self.rectangles])
            # no rotation
            self.lines += [f"(assert (or R{i} (<= posY{i} {self.H - self.rectangles[i].h})))" for i in range(self.n) if i != m]
            self.lines += [f"(assert (or R{i} (<= posX{i} {self.W - self.rectangles[i].w})))" for i in range(self.n) if i != m]
            self.lines.append(f"(assert (or R{m} (<= posX{m} {(self.W - self.rectangles[m].w)//2})))")
            self.lines.append(f"(assert (or R{m} (<= posY{m} {(self.H - self.rectangles[m].h)//2})))")
            # rotation
            self.lines += [f"(assert (or (not R{i}) (<= posY{i} {self.H - self.rectangles[i].w})))" for i in range(self.n) if i != m]
            self.lines += [f"(assert (or (not R{i}) (<= posX{i} {self.W - self.rectangles[i].h})))" for i in range(self.n) if i != m]
            self.lines.append(f"(assert (or (not R{m}) (<= posX{m} {(self.W - self.rectangles[m].h)//2})))")
            self.lines.append(f"(assert (or (not R{m}) (<= posY{m} {(self.H - self.rectangles[m].w)//2})))")
        else:
            # no rotation
            self.lines += [f"(assert (or R{i} (<= posY{i} {self.H - self.rectangles[i].h})))" for i in range(self.n)]
            self.lines += [f"(assert (or R{i} (<= posX{i} {self.W - self.rectangles[i].w})))" for i in range(self.n)]
            # rotation
            self.lines += [f"(assert (or (not R{i}) (<= posY{i} {self.H - self.rectangles[i].w})))" for i in range(self.n)]
            self.lines += [f"(assert (or (not R{i}) (<= posX{i} {self.W - self.rectangles[i].h})))" for i in range(self.n)]

    def add_non_overlapping_constraint(self, i, j, to_add=[True, True, True, True]):
        string = ""
        string_rotated = ""

        if to_add[0]:
            string += f" (or R{i} (<= (+ posX{i} {self.rectangles[i].w}) posX{j})) "
            string_rotated += f" (or (not R{i}) (<= (+ posX{i} {self.rectangles[i].w}) posX{j})) "
        if to_add[1]:
            string += f" (or R{i} (<= (+ posX{j} {self.rectangles[j].w}) posX{i})) "
            string_rotated += f" (or (not R{i}) (<= (+ posX{j} {self.rectangles[j].w}) posX{i})) "
        if to_add[2]:
            string += f" (or R{i} (<= (+ posY{i} {self.rectangles[i].h}) posY{j})) "
            string_rotated += f" (or (not R{i}) (<= (+ posY{i} {self.rectangles[i].h}) posY{j})) "
        if to_add[3]:
            string += f" (or R{i} (<= (+ posY{j} {self.rectangles[j].h}) posY{i})) "
            string_rotated += f" (or (not R{i}) (<= (+ posY{j} {self.rectangles[j].h}) posY{i})) "

        constraint = " ".join(string.split())
        constraint_rotated = " ".join(string_rotated.split())
        self.lines += [f"(assert (or {constraint}))"]
        self.lines += [f"(assert (or {constraint_rotated}))"]
    

    def check(self):
        super().check()
        self.lines.append(f"(get-value ({' '.join([f'R{i}' for i in range(self.n)])}))")
