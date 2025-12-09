import os
import textwrap
import tempfile

import z3

from efmc.frontends.c2efmc import c_to_efmc


def _write_tmp_c(code: str) -> str:
    fd, path = tempfile.mkstemp(suffix=".c")
    with os.fdopen(fd, "w") as f:
        f.write(textwrap.dedent(code))
    return path


def test_simple_while_translation():
    path = _write_tmp_c(
        """
        int main() {
            int x;
            x = 0;
            while (x < 3) { x = x + 1; }
            assert(x == 3);
        }
        """
    )
    try:
        ts = c_to_efmc(path)
        x = ts.variables[0]
        xp = ts.prime_variables[0]

        assert len(ts.variables) == 1
        assert str(x) == "x"
        assert str(xp) == "x!"

        _assert_equiv(ts.init, x == 0)
        _assert_equiv(ts.trans, z3.And(x < 3, xp == x + 1))
        _assert_equiv(ts.post, x == 3)
    finally:
        os.unlink(path)


def test_for_loop_normalization():
    path = _write_tmp_c(
        """
        int main() {
            int i;
            for (i = 0; i < 2; i = i + 1) { }
            assert(i == 2);
        }
        """
    )
    try:
        ts = c_to_efmc(path)
        i = ts.variables[0]
        ip = ts.prime_variables[0]

        _assert_equiv(ts.init, i == 0)
        _assert_equiv(ts.trans, z3.And(i < 2, ip == i + 1))
        _assert_equiv(ts.post, i == 2)
    finally:
        os.unlink(path)


def test_assume_added_to_guard():
    path = _write_tmp_c(
        """
        int main() {
            int x;
            x = 1;
            while (x < 5) { __VERIFIER_assume(x >= 0); x = x + 2; }
        }
        """
    )
    try:
        ts = c_to_efmc(path)
        x = ts.variables[0]
        xp = ts.prime_variables[0]

        # Transition must imply the assume guard
        solver = z3.Solver()
        solver.add(ts.trans, z3.Not(x >= 0))
        assert solver.check() == z3.unsat

        # And still carry the expected update
        _assert_equiv(ts.trans, z3.And(x < 5, x >= 0, xp == x + 2))
    finally:
        os.unlink(path)


def _assert_equiv(e1: z3.ExprRef, e2: z3.ExprRef):
    """Assert two boolean expressions are equivalent via a solver check."""
    s = z3.Solver()
    s.add(z3.Xor(e1, e2))
    assert s.check() == z3.unsat


if __name__ == "__main__":
    test_simple_while_translation()
    test_for_loop_normalization()
    test_assume_added_to_guard()