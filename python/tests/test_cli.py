"""The CLI report runs, and says the honest things it is supposed to say."""

from __future__ import annotations

from collatz_maxodd.__main__ import main, report


def test_report_runs_and_is_self_consistent():
    text = report(q_max=99, bound=2000, depth=5, mod2_depth=8)
    assert "HONESTY BANNER" in text
    assert "Nothing in this package is new mathematics" in text
    assert "Boehm & Sontacchi 1978" in text
    # the three corrections to the ground-truth doc must be visible in the report
    assert "the doc's hypothesis; FALSE" in text
    assert "'T4 recurses to higher powers of 3' is WRONG" in text
    assert "The unconditional version of the floor rule is FALSE" in text
    # and the sieve's own limitation
    assert "SATURATES" in text
    assert "CANNOT close the problem" in text
    assert "M >= q is NOT enough" in text


def test_report_shows_that_M_ge_q_breaks_T2():
    """The T2x row must actually show a failure ratio, not 100%."""
    text = report(q_max=99, bound=2000, depth=4, mod2_depth=6)
    (t2,) = [ln for ln in text.splitlines() if ln.startswith("T2  ")]
    (t2x,) = [ln for ln in text.splitlines() if ln.startswith("T2x ")]
    good, total = (int(x) for x in t2.split(":")[1].strip().split("/"))
    assert good == total > 0  # M > q: T2 always holds
    goodx, totalx = (int(x) for x in t2x.split(":")[1].split()[0].split("/"))
    assert goodx < totalx  # M >= q: the M = q fixed points break it


def test_report_contains_the_landmark_numbers():
    text = report(q_max=99, bound=2000, depth=6, mod2_depth=8)
    assert "1, 2, 3, 7, 12, 30, 85, 173" in text  # N(k)
    assert "[2, 8]" in text  # depth-1 mod 9 survivors
    assert "M = 17, 29 (mod 36)" in text  # T4
    assert "1/1, 2/1, 3/2, 8/5, 19/12" in text  # convergents
    assert "[1, 2, 7, 12, 53, 359, 665]" in text  # record depths


def test_main_entry_point(capsys):
    assert main(["--q-max", "49", "--bound", "1000", "--depth", "4", "--mod2-depth", "6"]) == 0
    out = capsys.readouterr().out
    assert "CYCLES FOUND" in out
    assert "CLAIMS CHECKED AGAINST EVERY CYCLE FOUND" in out
