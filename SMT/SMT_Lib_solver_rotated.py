from utils import PositionedRectangle, Rectangle
import numpy as np
from SMT_Lib_solver import SMT_Lib_solver

import sys
sys.path.append("../common")


class SMT_Lib_solver_rotated(SMT_Lib_solver):
    def __init__(self, W, H, rectangles, break_symmetries=False, timeout=300, logic="LIA", solver="z3"):
        super().__init__(W, H, rectangles, break_symmetries, timeout, logic, solver)


    def decisional_variables(self):
        super().decisional_variables()
        #R[i] means that rectangle i is rotated
        for i in range(self.n):
            self.lines.append(f"(declare-fun R{i} () Bool)")
            self.lines.append(f"(declare-fun W{i} () Int)")
            self.lines.append(f"(declare-fun H{i} () Int)")


    def domain(self):
        self.lines += [f"(assert (>= posX{i} 0))" for i in range(self.n)]
        self.lines += [f"(assert (>= posY{i} 0))" for i in range(self.n)]

        if self.break_symmetries:
            m = np.argmax([r.w * r.h for r in self.rectangles])
            # no rotation
            self.lines += [f"(assert (=> (not R{i}) (<= posX{i} {self.W - self.rectangles[i].w})))" for i in range(self.n) if i != m]
            self.lines += [f"(assert (=> (not R{i}) (<= posY{i} {self.H - self.rectangles[i].h})))" for i in range(self.n) if i != m]
            self.lines.append(f"(assert (=> (not R{m}) (<= posX{m} {(self.W - self.rectangles[m].w)//2})))")
            self.lines.append(f"(assert (=> (not R{m}) (<= posY{m} {(self.H - self.rectangles[m].h)//2})))")
            # rotation
            self.lines += [f"(assert (=> R{i} (<= posX{i} {self.W - self.rectangles[i].h})))" for i in range(self.n) if i != m]
            self.lines += [f"(assert (=> R{i} (<= posY{i} {self.H - self.rectangles[i].w})))" for i in range(self.n) if i != m]
            self.lines.append(f"(assert (=> R{m} (<= posX{m} {(self.W - self.rectangles[m].h)//2})))")
            self.lines.append(f"(assert (=> R{m} (<= posY{m} {(self.H - self.rectangles[m].w)//2})))")
        else:
            # no rotation
            self.lines += [f"(assert (=> (not R{i}) (<= posX{i} {self.W - self.rectangles[i].w})))" for i in range(self.n)]
            self.lines += [f"(assert (=> (not R{i}) (<= posY{i} {self.H - self.rectangles[i].h})))" for i in range(self.n)]
            # rotation
            self.lines += [f"(assert (=> R{i} (<= posX{i} {self.W - self.rectangles[i].h})))" for i in range(self.n)]
            self.lines += [f"(assert (=> R{i} (<= posY{i} {self.H - self.rectangles[i].w})))" for i in range(self.n)]


    def rotation_constraints(self):
        for i in range(self.n):
            self.lines += [f"(assert (=> (not R{i}) (= W{i} {self.rectangles[i].w})))"]
            self.lines += [f"(assert (=> (not R{i}) (= H{i} {self.rectangles[i].h})))"]
            self.lines += [f"(assert (=> R{i} (= W{i} {self.rectangles[i].h})))"]
            self.lines += [f"(assert (=> R{i} (= H{i} {self.rectangles[i].w})))"]


    def add_non_overlapping_constraint(self, i, j, to_add=[True, True, True, True]):
        string = ""
        if to_add[0]:
            string += f" (<= (+ posX{i} W{i}) posX{j}) "
        if to_add[1]:
            string += f" (<= (+ posX{j} W{j}) posX{i}) "
        if to_add[2]:
            string += f" (<= (+ posY{i} H{i}) posY{j}) "
        if to_add[3]:
            string += f" (<= (+ posY{j} H{j}) posY{i}) "

        constraint = " ".join(string.split())
        self.lines += [f"(assert (or {constraint}))"]


    def check(self):
        super().check()
        self.lines.append(f"(get-value ({' '.join([f'R{i}' for i in range(self.n)])}))")


    def create_SMT_file(self):
        self.write_logic()
        self.decisional_variables()
        self.domain()
        self.rotation_constraints()
        if self.break_symmetries:
            self.non_overlapping_constraints_SB()
        else:
            self.non_overlapping_constraints()
        self.check()

        with open(self.filename, "w") as f:
            for line in self.lines:
                f.write(line+"\n")


    def parse_solution(self, output_string):
        if "cvc5" in self.solver:
            output_string = output_string.replace(") (", "\n")

        output_list = output_string.split("\n")
        if "unsat" in output_list[0]:
            return []

        pos_xy = [s.split()[-1].split(")")[0] for s in output_list[1:-1]]
        x_values = [int(a) for a in pos_xy[:len(pos_xy)//3]]
        y_values = [int(a) for a in pos_xy[len(pos_xy)//3:2*len(pos_xy)//3]]
        R_values = [a.lower()=='true' for a in pos_xy[2*len(pos_xy)//3:]]

        true_rectangles = []
        for rect, rot in zip(self.rectangles, R_values):
            if rot:
                true_rectangles.append(Rectangle(rect.h, rect.w))
            else:
                true_rectangles.append(rect)

        return [PositionedRectangle(x, y, rect.w, rect.h) for x, y, rect in zip(x_values, y_values, true_rectangles)]
