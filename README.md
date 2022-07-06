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
