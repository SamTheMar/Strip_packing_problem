# Strip packing problem
The strip packing problem is a 2-dimensional geometric minimization problem. Given a set of axis-aligned rectangles and a strip of bounded width and infinite height, determine an overlapping-free packing of the rectangles into the strip minimizing its height. 

## Requirements
To analyze the data we produced, the following packages are sufficient:
 - ``numpy``
 - ``matplotlib``

### SAT
If you want to compute the SAT solutions yourself, you need the following Python package (in addition to the fundamental ones):
 - ``z3-solver``

To install it:
```
pip install z3-solver
```

### SMT
SMT uses SMT-LIB to interface with an external solver. Currently, the ``z3`` and ``cvc5`` solvers are supported. You need either one of these present in 
the system PATH. We recommend using ``z3``, as it performs better than ``cvc5``. Pre-built binaries for ``z3`` can be found [here](https://github.com/Z3Prover/z3), and for ``cvc5`` [here](https://github.com/cvc5/cvc5/releases/).

Other solvers may also be used, but they require some tweaking of the code to be used with the Python interface.

All SMT solutions here have been generated using ``z3``.

### CP and LP
If you want to compute the CP and LP solutions yourself, you need the following Python package (in addition to the fundamental ones):
 - ``minizinc``

To install it:
```
pip install minizinc
```

You also need an installation of Minizinc on your system.

For LP you need to install ``guroby`` and ``CPLEX`` solver on your minizinc installation

## Computation

### SAT and SMT
In order to compute the SAT and SMT solutions, you need to open the notebook ``computation.ipynb`` (in the folder ``common``) and execute it.

### CP 
In order to compute the CP solutions, you need to execute the following command from the root folder:
```
python CP/src/CP_interface.py -r <rotation> -o <ordering> -s <search_strategy> -t <restart_strategy>
```
or 
```
python CP/src/CP_interface.py --rotation <rotation> --ordering <ordering> --search_strategy <search_strategy> --restart_strategy <restart_strategy>
```
where :
- rotation can be only True or False
    - default is False
- ordering can be only True or False
    - default is True
- search_strategy can be only domw_deg, impact, input_order
    - default is input_order
- restart_strategy can be only luby, geometric, none
    - default is luby

### LP
In order to compute the LP solutions, you need to execute the following command from the root folder:
```
python LP/src/LP_interface.py -r <rotation> -o <ordering> -s <solver>
```
or
```
python LP/src/LP_interface.py --rotation <rotation> --ordering <ordering> --solver <solver>
```
where :
- rotation can be only True or False
    - default is False
- ordering can be only True or False
    - default is True
- solver can be only gurobi or coin-bc or cplex
    - default is gurobi

## Visualization
You can visualize:
- the results of the computation using ``visualize_examples.ipynb``
- all the analysis using ``analysis.ipynb``