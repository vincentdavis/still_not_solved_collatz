"""``collatz_maxodd`` -- residue restrictions on the largest odd element of a 3n+q cycle.

The idea under study: a Collatz (or ``3n+q``) cycle must have a largest **odd**
element ``M``, and large classes of numbers can be excluded from being that ``M``.

This package is an exploration tool, not a proof.  Every claim it encodes is
elementary and almost certainly already in the Collatz literature -- see the
per-module "prior art" notes and ``docs/GROUND_TRUTH.md``.  Nothing here closes,
or comes anywhere near closing, the Collatz conjecture.

Modules
-------
``syracuse``   the odd step ``S_q``, forward/backward maps, the predecessor lemma
``cycles``     exhaustive search for all ``S_q``-cycles with ``M <= bound``
``sieve``      residue sieves on ``M`` (mod 4, 12, 36, ``3^k``; and mod ``2^a``)
``backtree``   the backward tree from a hypothetical ``M``, with the exact T6 test
``cycleeq``    the cycle equation, ``2^B/3^L``, ``log2 3`` convergents, length bounds
"""

from __future__ import annotations

from .backtree import (
    admissible_halving_vectors,
    backward_chains,
    c_constant,
    count_admissible_halving_vectors,
    floor_bound,
    floor_rule_safe_M,
    floor_rule_threshold,
    size_admissible,
    y_value,
)
from .cycleeq import (
    BARINA_2025_LIMIT,
    best_upper_approximations,
    check_cycle_equation,
    cycle_constant,
    length_admissible,
    log2_3,
    log2_3_cf,
    log2_3_convergents,
    min_B_for_L,
    product_identity,
    smallest_admissible_length,
)
from .cycles import Cycle, find_cycles, find_cycles_multi
from .sieve import (
    Verdict,
    can_be_max_odd,
    combined_residues,
    combined_surviving_density,
    surviving_residues_mod2,
    surviving_residues_mod3,
    surviving_residues_mod3_no_size,
    t1_ok,
    t2_residue_ok,
    t3_ok,
    t4_ok,
    t8_ok,
)
from .syracuse import (
    check_q,
    count_predecessors_below,
    forward_exponents,
    forward_orbit,
    odd_predecessors,
    predecessor_at,
    predecessor_parity,
    smaller_predecessor,
    syracuse,
    syracuse_with_exponent,
    v2,
)

__version__ = "0.1.0"

__all__ = [
    "__version__",
    # syracuse
    "v2",
    "check_q",
    "syracuse",
    "syracuse_with_exponent",
    "forward_orbit",
    "forward_exponents",
    "predecessor_parity",
    "predecessor_at",
    "odd_predecessors",
    "smaller_predecessor",
    "count_predecessors_below",
    # cycles
    "Cycle",
    "find_cycles",
    "find_cycles_multi",
    # sieve
    "Verdict",
    "can_be_max_odd",
    "t1_ok",
    "t2_residue_ok",
    "t3_ok",
    "t4_ok",
    "t8_ok",
    "surviving_residues_mod3",
    "surviving_residues_mod3_no_size",
    "surviving_residues_mod2",
    "combined_residues",
    "combined_surviving_density",
    # backtree
    "floor_bound",
    "c_constant",
    "y_value",
    "size_admissible",
    "admissible_halving_vectors",
    "count_admissible_halving_vectors",
    "floor_rule_threshold",
    "floor_rule_safe_M",
    "backward_chains",
    # cycleeq
    "cycle_constant",
    "check_cycle_equation",
    "product_identity",
    "log2_3",
    "log2_3_cf",
    "log2_3_convergents",
    "best_upper_approximations",
    "min_B_for_L",
    "length_admissible",
    "smallest_admissible_length",
    "BARINA_2025_LIMIT",
]
