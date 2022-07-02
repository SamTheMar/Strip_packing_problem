from asyncio import constants
import subprocess
import numpy as np

import sys
sys.path.append("../common")
from utils import PositionedRectangle


class SMT_Lib_solver():
    def __init__(self, W, H, rectangles, break_symmetries=False, logic="AUFLIA", solver="z3"):
        self.W = W
        self.H = H
        self.rectangles = rectangles
        self.n = len(rectangles)
        self.break_symmetries = break_symmetries
        self.logic = logic
        self.solver = solver
        self.filename = "SMT_LIB.smt2"
        self.lines = []


    def set_logic(self, logic):
        self.lines.append(f"(set-logic {logic})")


    def decisional_variables(self):
        self.lines.append("(declare-fun posX (Int) Int)")
        self.lines.append("(declare-fun posY (Int) Int)")
        self.lines.append("(declare-fun H () Int)")


    def domain(self):
        self.lines += [f"(assert (>= (select posX {i}) 0))" for i in range(self.n)]
        self.lines += [f"(assert (>= (select posY {i}) 0))" for i in range(self.n)]
        if self.break_symmetries:
            m = np.argmax([r.w * r.h for r in self.rectangles])
            self.lines += [f"(assert (<= (+ (select posX {i}) {self.rectangles[i].w}) {self.W}))" for i in range(self.n) if i != m]
            self.lines.append(f"(assert (<= (+ (select posX {m}) {self.rectangles[m].w}) {self.W // 2}))")
        else:
            self.lines += [f"(assert (<= (+ (select posX {i}) {self.rectangles[i].w}) {self.W}))" for i in range(self.n)]
        self.lines += [f"(assert (<= (+ (select posY {i}) {self.rectangles[i].h}) {self.H}))" for i in range(self.n)]


    def add_non_overlapping_constraints(self, i, j, to_add = [True, True, True, True]):
        string = ""
        if to_add[0]:
            string += f" (<= (+ (select posX {i}) {self.rectangles[i].w}) (select posX {j})) "
        if to_add[1]:
            string += f" (<= (+ (select posX {j}) {self.rectangles[j].w}) (select posX {i})) "
        if to_add[2]:
            string += f" (<= (+ (select posY {i}) {self.rectangles[i].h}) (select posY {j})) "
        if to_add[3]:
            string += f" (<= (+ (select posY {j}) {self.rectangles[j].h}) (select posY {i})) "
            
        constraint = " ".join(string.split())
        self.lines += [f"(assert (or {constraint}))"]


    def non_overlapping_constraints(self):
        for j in range(self.n):
            for i in range(j):
                self.add_non_overlapping_constraints(i, j)
                

    def non_overlapping_constraints_SB(self):
        m = np.argmax([r.w * r.h for r in self.rectangles])

        for j in range(self.n):
            for i in range(j):
                # LS: Reducing the domain for the largest rectangle
                if j == m and self.rectangles[i].w > (self.W - self.rectangles[m].w)//2:
                        self.add_non_overlapping_constraint(i, j, [False, True, True, True])
                # SR: Breaking symmetries for same-sized rectangles
                elif self.rectangles[i].w == self.rectangles[j].w and self.rectangles[i].h == self.rectangles[j].h:
                    self.add_non_overlapping_constraint(i, j, [True, False, True, True])
                # LR (horizontal)
                elif self.rectangles[i].w + self.rectangles[j].w > self.W:
                    self.add_non_overlapping_constraint(i, j, [False, False, True, True])
                else:
                    self.add_non_overlapping_constraint(i, j)


    def check(self):
        self.lines.append("(check-sat)")
        self.lines.append(f"(get-value ({' '.join([f'(select posX {i})' for i in range(self.n)])}))")
        self.lines.append(f"(get-value ({' '.join([f'(select posY {i})' for i in range(self.n)])}))")


    def create_SMT_file(self):
        self.set_logic(self.logic.upper())
        self.decisional_variables()
        self.domain()
        self.non_overlapping_constraints()
        self.check()

        with open(self.filename, "w") as f:
            for line in self.lines:
                f.write(line+"\n")
    

    def parse_solution(self, output_string):
        output_list = output_string.split("\n")
        if "unsat" in output_list[0]:
            return []
        pos_xy = [int(s.split()[-1].split(")")[0]) for s in output_list[1:-1]]
        x_values = pos_xy[:len(pos_xy)//2]
        y_values = pos_xy[len(pos_xy)//2:]
        
        return [PositionedRectangle(x, y, rect.w, rect.h) for x, y, rect in zip(x_values, y_values, self.rectangles)]


    def solve(self):
        self.create_SMT_file()
        result = subprocess.run([self.solver, self.filename], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        output_string = str(result.stdout, encoding="ASCII")
        return self.parse_solution(output_string)


