Termination Verification
========================

Overview
--------

Termination verification determines whether a program loop will eventually terminate or run forever. EFMC provides template-based termination verification using two complementary approaches:

1. **Ranking Function Synthesis**: Proves termination by finding a ranking function that decreases on each loop iteration
2. **Recurrence Set Synthesis**: Proves non-termination by finding a recurrence set (a set of states that the loop can return to infinitely often)

The termination prover supports bit-vector programs and uses various template-based techniques for both termination and non-termination analysis.

Ranking Functions
-----------------

A ranking function R(x) proves termination if:

1. **Base Case**: R(x) ≥ 0 for all initial states
2. **Decreasing**: For each transition, R(x') < R(x) when the loop guard is true
3. **Bounded**: R(x) is bounded from below (typically R(x) ≥ 0)

If such a ranking function exists, the loop must terminate because the ranking function cannot decrease indefinitely.

Supported Ranking Function Templates
-------------------------------------

**Linear Ranking Functions:**
- Simple linear combinations: R(x) = a₁x₁ + a₂x₂ + ... + c
- Suitable for programs with linear arithmetic

**Lexicographic Ranking Functions:**
- Multiple components: R(x) = (R₁(x), R₂(x), ...)
- Decreases lexicographically: first component decreases, or if it stays the same, second decreases, etc.
- More expressive than linear ranking functions

**Conditional Ranking Functions:**
- Different ranking functions for different program branches
- Handles programs with multiple execution paths

Recurrence Sets
---------------

A recurrence set S(x) proves non-termination if:

1. **Reachability**: S(x) is reachable from initial states
2. **Closure**: From any state in S(x), there exists a transition back to S(x)
3. **Progress**: The transition maintains the loop guard (loop continues)

If such a recurrence set exists, the loop can execute infinitely often.

Supported Recurrence Set Templates
-----------------------------------

**Linear Recurrence Sets:**
- Linear constraints defining the recurrence set
- Suitable for programs with linear arithmetic

**Interval Recurrence Sets:**
- Interval constraints defining the recurrence set
- More general than linear constraints

**Disjunctive Recurrence Sets:**
- Union of multiple recurrence sets
- Handles complex non-termination patterns

Usage
-----

The termination prover is used programmatically:

.. code-block:: python

   from efmc.engines.ef.termination import TerminationProver
   from efmc.sts import TransitionSystem
   
   # Create transition system
   sts = TransitionSystem(...)
   
   # Create termination prover
   prover = TerminationProver(sts, solver='z3api')
   
   # Set ranking function template
   prover.set_ranking_template('bv_linear_ranking')
   
   # Try to prove termination
   result = prover.prove_termination(timeout=60)
   
   if result.result:
       print("Termination proven!")
       ranking_func = prover._extract_ranking_function()
       print(f"Ranking function: {ranking_func}")
   else:
       print("Could not prove termination")
       if result.error:
           print(f"Error: {result.error}")

Proving Non-Termination
------------------------

.. code-block:: python

   # Set recurrence set template
   prover.set_recurrence_template('bv_linear_recurrence')
   
   # Try to prove non-termination
   result = prover.prove_non_termination(timeout=60)
   
   if result.result:
       print("Non-termination proven!")
       recurrence_set = result.recurrence_set
       print(f"Recurrence set: {recurrence_set}")
   else:
       print("Could not prove non-termination")

Comprehensive Analysis
----------------------

The termination API provides a high-level function for comprehensive analysis:

.. code-block:: python

   from efmc.engines.ef.termination import analyze_termination
   
   results = analyze_termination(
       sts,
       ranking_templates=['bv_linear_ranking', 'bv_lexicographic_ranking'],
       recurrence_templates=['bv_linear_recurrence'],
       timeout=120
   )
   
   if results['termination_proven']:
       print("Termination proven!")
       print(f"Template used: {results['ranking_template_used']}")
       print(f"Ranking function: {results['ranking_function']}")
   elif results['non_termination_proven']:
       print("Non-termination proven!")
       print(f"Template used: {results['recurrence_template_used']}")
       print(f"Recurrence set: {results['recurrence_set']}")
   else:
       print("Could not determine termination status")
       if results['errors']:
           print(f"Errors: {results['errors']}")

Configuration Options
---------------------

**Solver Options:**
- ``solver``: Backend SMT solver ('z3api', 'cvc5', etc.)

**Validation Options:**
- ``validate_ranking_function``: Validate synthesized ranking functions
- ``validate_recurrence_set``: Validate synthesized recurrence sets

**Template Options:**
- ``num_components``: Number of components for lexicographic ranking functions
- ``num_branches``: Number of branches for conditional ranking functions

**Debugging Options:**
- ``print_vc``: Print verification conditions for debugging

Bit-Vector Support
------------------

The termination prover is optimized for bit-vector programs:

- Supports signed and unsigned bit-vector arithmetic
- Handles bit-vector overflow and underflow
- Uses bit-vector specific ranking function templates
- Supports bit-vector recurrence set templates

Limitations
-----------

- Currently optimized for single-loop programs
- May require manual template selection for complex programs
- Performance depends on the chosen template and solver

Related Work
------------

- Bradley, A. R., Manna, Z., & Sipma, H. B. (2005). Termination of polynomial programs. VMCAI 2005.
- Cook, B., Podelski, A., & Rybalchenko, A. (2006). Termination proofs for systems code. PLDI 2006.
- Heizmann, M., et al. (2013). Software model checking for people who love automata. CAV 2013.
- Larraz, D., et al. (2014). Proving non-termination using Max-SMT. CAV 2014.

