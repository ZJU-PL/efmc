.. _smttools:

SMT Tools
=========

The ``smttools`` module provides interfaces to various SMT solvers and related utilities for handling SMT-LIB format formulas.

Architecture
------------

.. code-block::

   efmc/smttools/
   ├── smtlib_solver.py    # SMT-LIB interactive process interface
   ├── sygus_solver.py     # SyGuS solver interface
   ├── pysmt_solver.py     # PySMT-based solver wrapper
   ├── mapped_blast.py     # Bit-blasting utilities
   ├── smt_exceptions.py   # Exception definitions
   └── __init__.py         # Module exports

SMT-LIB Solver Interface
------------------------

The ``smtlib_solver`` module provides an interactive interface to SMT solvers that support the SMT-LIB 2 format.

SmtlibProc
~~~~~~~~~~

Main class for interacting with SMT-LIB compliant solvers.

.. code-block:: python

   from efmc.smttools.smtlib_solver import SmtlibProc

   # Create solver interface
   solver = SmtlibProc("z3 -smt2 -in")

   # Start the solver process
   solver.start()

   # Send commands and get responses
   solver.write("(set-logic QF_BV)")
   response = solver.read()

   # Check satisfiability
   solver.write("(check-sat)")
   response = solver.read()  # "sat", "unsat", or "unknown"

   # Close the solver
   solver.close()

Available Solvers
~~~~~~~~~~~~~~~~~

EFMC supports the following SMT solvers:

- **Z3**: Microsoft Research's SMT solver
- **CVC5**: The SMT solver from Stanford AI Lab
- **Yices2**: SRI's SMT solver
- **Bitwuzla**: The SMT solver for bit-vectors and arrays
- **MathSAT**: The MathSAT5 SMT solver

Example usage:

.. code-block:: python

   from efmc.smttools.smtlib_solver import SmtlibProc

   # Use Z3
   z3_solver = SmtlibProc("z3 -smt2 -in")

   # Use CVC5
   cvc5_solver = SmtlibProc("cvc5 --lang=smt2 --incremental")

   # Use Bitwuzla
   bitwuzla_solver = SmtlibProc("bitwuzla --sat")

SyGuS Solver Interface
----------------------

The ``sygus_solver`` module provides support for Syntax-Guided Synthesis (SyGuS) problems.

.. code-block:: python

   from efmc.smttools.sygus_solver import SyGuSSolver

   solver = SyGuSSolver()
   solver.set_options([
       "--generate-synth-assumptions",
       "--cegqi-si-all"
   ])

   # Submit synthesis problem
   solver.write("(set-logic LIA)")
   solver.write("(synth-fun f ((x Int)) Int)")

   # Get solution
   solution = solver.get_synth_solution()

PySMT Integration
-----------------

The ``pysmt_solver`` module provides integration with PySMT, enabling solver-agnostic SMT solving.

.. code-block:: python

   from pysmt.shortcuts import Symbol, Int, GT, Plus
   from efmc.smttools.pysmt_solver import PySMTZ3Solver

   # Create solver
   solver = PySMTZ3Solver()

   # Create formula
   x = Symbol("x", Int())
   y = Symbol("y", Int())

   formula = GT(Plus(x, y), Int(0))

   # Solve
   solver.add_assertion(formula)
   result = solver.solve()

Mapped Blast
------------

The ``mapped_blast`` module provides utilities for bit-blasting SMT formulas, converting them to CNF format.

.. code-block:: python

   from efmc.smttools.mapped_blast import BitBlaster

   blaster = BitBlaster()
   cnf = blaster.bv_to_cnf(bv_formula)
   blaster.dump_cnf(cnf, "output.cnf")

Exception Handling
------------------

Custom exceptions for SMT-related errors:

.. code-block:: python

   from efmc.smttools.smt_exceptions import SolverError, SolverTimeout

   try:
       result = solver.solve()
   except SolverTimeout:
       print("Solver timed out")
   except SolverError as e:
       print(f"Solver error: {e}")

Supported Logics
----------------

The following SMT logics are supported:

- **QF_BV**: Quantifier-free bit-vectors
- **QF_UFBV**: Unbounded bit-vectors
- **QF_LIA**: Quantifier-free linear integer arithmetic
- **QF_LRA**: Quantifier-free linear real arithmetic
- **QF_NIA**: Non-linear integer arithmetic
- **QF_NRA**: Non-linear real arithmetic
- **QF_FP**: Floating-point arithmetic
- **QF_SLIA**: String length integer arithmetic

API Reference
-------------

.. automodule:: efmc.smttools.smtlib_solver
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: efmc.smttools.sygus_solver
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: efmc.smttools.pysmt_solver
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: efmc.smttools.mapped_blast
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: efmc.smttools.smt_exceptions
   :members:
   :undoc-members:
   :show-inheritance:
