.. _frontend:

Frontends
=========

The ``frontends`` module provides parsers for various input formats, converting them into EFMC's internal transition system representation.

Supported Formats
-----------------

EFMC supports the following input formats:

1. **CHC (Constrained Horn Clauses)** - ``.smt2``
2. **SyGuS (Syntax-Guided Synthesis)** - ``.sy``, ``.sl``
3. **Boogie** - ``.bpl``
4. **C** - ``.c``
5. **VMT** - ``.vmt`` (planned)
6. **Btor2** - ``.btor2`` (planned)

Architecture
------------

.. code-block::

   efmc/frontends/
   ├── chc_parser.py          # CHC format parser
   ├── mini_sygus_parser.py   # SyGuS format parser
   ├── boogie2efmc.py         # Boogie frontend
   ├── c2efmc.py              # C frontend
   ├── c2chc.py               # C to CHC converter
   ├── chc2c.py               # CHC to C converter
   ├── btor2chc.py            # Btor2 to CHC converter
   ├── chc_parser.py          # CHC parser utilities
   └── chc2c/                 # CHC2C subpackage
       ├── BaseCHC2C.py       # Base class
       ├── LinearCHC2C.py     # Linear CHC handling
       ├── NonLinearCHC2C.py  # Non-linear CHC handling
       └── chc2c.py           # Main converter

CHC Parser
----------

The CHC (Constrained Horn Clauses) parser handles SMT-LIB files with constrained Horn clauses.

Usage
~~~~~

.. code-block:: python

   from efmc.frontends import parse_chc

   # Parse CHC file
   all_vars, init, trans, post = parse_chc("program.smt2", to_real_type=False)

   # Create transition system
   from efmc.sts import TransitionSystem
   sts = TransitionSystem()
   sts.from_z3_cnts([all_vars, init, trans, post])

CHC Format
~~~~~~~~~~

A typical CHC file has the following structure:

.. code-block:: smt2

   (set-logic QF_LIA)
   (declare-fun x () Int)
   (declare-fun y () Int)

   ; Init: x = 0
   (assert (= x 0))

   ; Transition: y' = y + x, x' = x + 1
   (assert (=> true (= y (+ y x))))

   ; Query: y < 0
   (query (=> true (< y 0)))

The CHC representation consists of:
- ``all_vars``: All variables in the system
- ``init``: Initial state predicate
- ``trans``: Transition relation
- ``post``: Post-condition (query)

SyGuS Parser
------------

The SyGuS parser handles Syntax-Guided Synthesis files, specifically the invariant track.

Usage
~~~~~

.. code-block:: python

   from efmc.frontends import parse_sygus

   # Parse SyGuS file
   all_vars, init, trans, post = parse_sygus("invariant.sy", to_real_type=False)

SyGuS Format
~~~~~~~~~~~~

A typical SyGuS invariant file:

.. code-block:: sygus

   (set-logic QF_LIA)
   (set-option :syntax-restrictions :inv)
   (declare-fun x () Int)
   (declare-fun inv ((x Int)) Bool)
   (assert (inv 0))
   (assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
   (check-synth)

Boogie Frontend
---------------

The Boogie frontend handles Boogie intermediate verification language files.

Usage
~~~~~

.. code-block:: python

   from efmc.frontends import parse_boogie

   # Parse Boogie file
   sts = parse_boogie("program.bpl")

Boogie Format
~~~~~~~~~~~~~

A typical Boogie program:

.. code-block:: boogie

   var x: int;
   var y: int;

   procedure main()
     requires x >= 0;
     ensures y >= 0;
   {
     y := x;
     while (x > 0)
       invariant y >= 0;
     {
       y := y - 1;
       x := x - 1;
     }
   }

C Frontend
----------

The C frontend parses C programs with annotations for verification.

Usage
~~~~~

.. code-block:: python

   from efmc.frontends import parse_c

   # Parse C file
   sts = parse_c("program.c")

C Format
~~~~~~~~

A typical annotated C program:

.. code-block:: c

   /*@
     requires x >= 0;
     ensures \result >= 0;
   @*/
   int foo(int x) {
     int y = x;
     while (x > 0) {
       x = x - 1;
     }
     return y;
   }

Conversion Tools
----------------

C to CHC
~~~~~~~~

Convert C programs to Constrained Horn Clauses:

.. code-block:: python

   from efmc.frontends.c2chc import C2CHC

   converter = C2CHC()
   converter.convert("program.c", "output.smt2")

CHC to C
~~~~~~~~

Convert CHC back to C:

.. code-block:: python

   from efmc.frontends.chc2c import CHC2C

   converter = CHC2C()
   converter.convert("program.smt2", "output.c")

Btor2 to CHC
~~~~~~~~~~~~

Convert Btor2 (hardware description) to CHC:

.. code-block:: python

   from efmc.frontends.btor2chc import Btor2CHC

   converter = Btor2CHC()
   converter.convert("design.btor2", "output.smt2")

API Reference
-------------

.. automodule:: efmc.frontends
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: efmc.frontends.chc_parser
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: efmc.frontends.mini_sygus_parser
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: efmc.frontends.boogie2efmc
   :members:
   :undoc-members:
   :show-inheritance:

.. automodule:: efmc.frontends.c2efmc
   :members:
   :undoc-members:
   :show-inheritance:
