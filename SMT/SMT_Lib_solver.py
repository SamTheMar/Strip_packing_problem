import subprocess

import sys
sys.path.append("../common")
from utils import PositionedRectangle


class SMT_Lib_solver():
    def __init__(self, W, H, rectangles, logic="AUFLIA", solver="z3"):
        self.W = W
        self.H = H
        self.rectangles = rectangles
        self.n = len(rectangles)
        self.lines = []
        self.solver = solver
        self.filename = "SMT_LIB.smt2"
        self.set_logic(logic.upper())


    def set_logic(self, logic):
        self.lines.append(f"(set-logic {logic})")


    def decisional_variables(self):
        self.lines.append("(declare-fun posX (Int) Int)")
        self.lines.append("(declare-fun posY (Int) Int)")
        self.lines.append("(declare-fun H () Int)")


    def domain(self):
        self.lines += [f"(assert (>= (select posX {i}) 0))" for i in range(self.n)]
        self.lines += [f"(assert (>= (select posY {i}) 0))" for i in range(self.n)]
        self.lines += [f"(assert (<= (+ (select posX {i}) {self.rectangles[i].w}) {self.W}))" for i in range(self.n)]
        self.lines += [f"(assert (<= (+ (select posY {i}) {self.rectangles[i].h}) {self.H}))" for i in range(self.n)]


    def non_overlapping_constraints(self):
        for j in range(self.n):
            for i in range(j):
                self.lines += [" ".join(f"""(assert (or (<= (+ (select posX {i}) {self.rectangles[i].w}) (select posX {j}))
                                                        (<= (+ (select posX {j}) {self.rectangles[j].w}) (select posX {i}))
                                                        (<= (+ (select posY {i}) {self.rectangles[i].h}) (select posY {j}))
                                                        (<= (+ (select posY {j}) {self.rectangles[j].h}) (select posY {i}))))""".split())
        ]


    def check(self):
        self.lines.append("(check-sat)")
        self.lines.append(f"(get-value ({' '.join([f'(select posX {i})' for i in range(self.n)])}))")
        self.lines.append(f"(get-value ({' '.join([f'(select posY {i})' for i in range(self.n)])}))")


    def create_SMT_file(self):
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
            return [], []
        pos_xy = [int(s.split()[-1].split(")")[0]) for s in output_list[1:-1]]
        x_values = pos_xy[:len(pos_xy)//2]
        y_values = pos_xy[len(pos_xy)//2:]
        
        return [PositionedRectangle(x, y, rect.w, rect.h) for x, y, rect in zip(x_values, y_values, self.rectangles)]


    def solve(self):
        self.create_SMT_file()
        result = subprocess.run([self.solver, self.filename], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        output_string = str(result.stdout, encoding="ASCII")
        return self.parse_solution(output_string)


