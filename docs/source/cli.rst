.. _cli:

Command-Line Interface
======================

EFMC provides three main command-line tools:

1. ``efmc`` - The main software model checker
2. ``efsmt`` - Exists-Forall SMT solver
3. ``polyhorn`` - Ranking function synthesis for termination

efmc
----

The ``efmc`` command is the primary interface for software model checking. It supports multiple input formats and verification engines.

Usage
~~~~~

.. code-block:: bash

   efmc --file <input_file> [options]

Input Formats
~~~~~~~~~~~~~

EFMC automatically detects the input format based on file extension:

- ``.smt2`` - Constrained Horn Clauses (CHC) format
- ``.sy`` or ``.sl`` - SyGuS invariant track format
- ``.bpl`` - Boogie intermediate verification language
- ``.c`` - C source code

Alternatively, you can explicitly specify the language:

.. code-block:: bash

   efmc --file program.smt2 --lang chc
   efmc --file program.sy --lang sygus
   efmc --file program.bpl --lang boogie
   efmc --file program.c --lang c

Verification Engines
~~~~~~~~~~~~~~~~~~~~

Use the ``--engine`` option to select a verification engine:

.. code-block:: bash

   efmc --file program.smt2 --engine ef        # Template-based (default)
   efmc --file program.smt2 --engine pdr       # Property-Directed Reachability
   efmc --file program.smt2 --engine kind      # K-Induction
   efmc --file program.smt2 --engine qi        # Quantifier Instantiation
   efmc --file program.smt2 --engine houdini   # Houdini algorithm
   efmc --file program.smt2 --engine abduction # Abductive inference
   efmc --file program.smt2 --engine bdd       # BDD-based verification
   efmc --file program.smt2 --engine predabs   # Predicate abstraction
   efmc --file program.smt2 --engine symabs    # Symbolic abstraction
   efmc --file program.smt2 --engine llm4inv   # LLM-guided invariant synthesis
   efmc --file program.smt2 --engine qe        # Quantifier elimination

Template-Based Verification Options
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When using the ``ef`` engine, you can specify templates for invariant generation:

Integer/Real templates:

.. code-block:: bash

   efmc --file program.smt2 --template interval       # Interval domain
   efmc --file program.smt2 --template power_interval # Powers of intervals
   efmc --file program.smt2 --template zone           # Zone domain
   efmc --file program.smt2 --template octagon         # Octagon domain
   efmc --file program.smt2 --template affine          # Affine relations
   efmc --file program.smt2 --template power_affine    # Powers of affine
   efmc --file program.smt2 --template poly            # Polynomial

Bitvector templates:

.. code-block:: bash

   efmc --file program.smt2 --template bv_interval      # BV intervals
   efmc --file program.smt2 --template bv_zone          # BV zones
   efmc --file program.smt2 --template bv_octagon       # BV octagons
   efmc --file program.smt2 --template bv_poly          # BV polynomials
   efmc --file program.smt2 --template bv_pattern       # Bit patterns
   efmc --file program.smt2 --template bv_xor_parity    # XOR/parity properties

SMT Solver Options
~~~~~~~~~~~~~~~~~~

EFMC supports multiple SMT solvers for the exists-forall SMT problems:

.. code-block:: bash

   # Quantifier instantiation approaches
   efmc --file program.smt2 --efsmt-solver z3api     # Z3 Python API (default)
   efmc --file program.smt2 --efsmt-solver z3        # Z3 via SMT-LIB
   efmc --file program.smt2 --efsmt-solver cvc5      # CVC5
   efmc --file program.smt2 --efsmt-solver yices2    # Yices2

   # Bit-blasting approaches
   efmc --file program.smt2 --efsmt-solver z3qbf     # Z3 QBF
   efmc --file program.smt2 --efsmt-solver caqe      # CAQE

   # CEGIS approach
   efmc --file program.smt2 --efsmt-solver cegis     # CEGIS with PySMT

LLM4Inv Options
~~~~~~~~~~~~~~~

For the LLM-guided invariant synthesis engine:

.. code-block:: bash

   # Local models
   efmc --file program.smt2 --engine llm4inv --llm4inv-local-provider lm-studio
   efmc --file program.smt2 --engine llm4inv --llm4inv-local-model qwen/qwen3-coder-30b

   # Remote models
   efmc --file program.smt2 --engine llm4inv --llm4inv-provider remote
   efmc --file program.smt2 --engine llm4inv --llm4inv-remote-model deepseek-v3

   # Generation parameters
   efmc --file program.smt2 --engine llm4inv --llm4inv-temperature 0.1
   efmc --file program.smt2 --engine llm4inv --llm4inv-max-candidates-per-iter 5
   efmc --file program.smt2 --engine llm4inv --llm4inv-max-iterations 10

Logging
~~~~~~~

Control verbosity with ``--log-level``:

.. code-block:: bash

   efmc --file program.smt2 --log-level DEBUG
   efmc --file program.smt2 --log-level INFO     # default
   efmc --file program.smt2 --log-level WARNING
   efmc --file program.smt2 --log-level ERROR

efsmt
-----

The ``efsmt`` command is a specialized solver for Exists-Forall SMT problems.

Usage
~~~~~

.. code-block:: bash

   efsmt --file <query.smt2> <solver> [options]

Example
~~~~~~~

.. code-block:: bash

   efsmt --file query.smt2 z3 --logic BV
   efsmt --file query.smt2 z3 --dump-smt2
   efsmt --file query.smt2 z3 --parallel

Options
~~~~~~~

- ``--logic``: The SMT logic (BV, UFBV, LIA, LRA, NIA, NRA, FP)
- ``--parallel``: Use parallel solving (BV logic only)
- ``--timeout``: Timeout in seconds
- ``--dump-smt2``: Dump the EFSMT query in SMT2 format
- ``--dump-qbf``: Dump the query in QBF format
- ``--dump-cnf``: Dump bit-blasted formula in CNF format

polyhorn
--------

The ``polyhorn`` command is used for ranking function synthesis and termination analysis.

Usage
~~~~~

.. code-block:: bash

   polyhorn --file <program.bpl> [options]

See :ref:`polyhorn` for detailed documentation.

Output
------

EFMC outputs verification results in a simple format:

- ``safe``: The property holds; an invariant may be printed
- ``unsafe``: A counterexample was found
- ``unknown``: Verification could not complete

Examples
--------

Basic verification:

.. code-block:: bash

   $ efmc --file examples/loop.smt2
   safe
   Invariant: x >= 0

Finding a counterexample:

.. code-block:: bash

   $ efmc --file examples/overflow.smt2
   unsafe
   Counterexample: x = 18446744073709551615

Debugging with verbose output:

.. code-block:: bash

   $ efmc --file examples/loop.smt2 --log-level DEBUG
   2024-01-10 10:30:00 - efmc - INFO - Parsing CHC file...
   2024-01-10 10:30:00 - efmc - INFO - CHC file parsing completed
   2024-01-10 10:30:00 - efmc - INFO - Starting template-based verification...
   ...
