# collatz_maxodd

Exploration tools for **residue restrictions on the largest odd element `M` of a
`3n+q` cycle**.

    S_q(n) = (3n + q) / 2^b,   b = v2(3n + q) >= 1,   n odd, q odd, 3 does not divide q

`L` = number of odd elements, `M` = largest odd element, `B` = total halvings.
Classical Collatz is `q = 1`.  Notation follows `../docs/GROUND_TRUTH.md`.

## Honesty first

**Nothing in this package is new mathematics.**  Every claim it encodes is
elementary and is already in the Collatz literature:

| claim | prior art |
|---|---|
| T0 (no odd multiple of 3 has an odd predecessor) | Kaneda, *Fibonacci Quart.* 53(2) (2015) 168-174, states it verbatim for general `d`; it is why Tao's Syracuse map lives on the odds coprime to 3 (Tao, *Forum of Math. Pi* 10 (2022) e12). |
| T1 (the cycle maximum needs `>= 2` halvings) | Brox's "descending" condition, *Acta Arith.* 92 (2000) 181-188; the local-max decomposition of Simons & de Weger, *Acta Arith.* 117 (2005) 51-70. |
| T2 (the step into the maximum is a `b = 1` step) | Built into the increase-run structure of Simons-de Weger; Kaneda Thm 2.1 uses the same inverse map. |
| T3, T4, T5, T8 | One-line corollaries of the above.  Not found written verbatim, which is the weakest possible form of novelty.  Do not call them results. |
| T6 (the `2^{B_k}` vs `3^k` prefix inequality) | Kaneda 2015 Thm 2.1 (ineq. 2.3), Eliahou *Discrete Math.* 118 (1993) 45-56, Halbeisen & Hungerbuehler *Acta Arith.* 78 (1997), Simons-de Weger 2005, Hercher *JIS* 26 (2023) Art. 23.3.5. |
| T7 (the cycle equation and `2^B/3^L`) | Boehm & Sontacchi, *Atti Accad. Naz. Lincei* 64 (1978) 260-264 -- already formalised in Lean at ccchallenge.org -- plus Crandall, *Math. Comp.* 32 (1978) 1281-1292. |

**The sieve cannot close the problem.**  The 2-adic (forward) half saturates at a
limiting density of `0.2863153965` of the odd numbers -- 1.80 bits, forever, no
matter how deep you go.  The 3-adic (backward) half keeps cutting, but only
geometrically in the depth `k`, while the modulus grows at `log2 3 = 1.585` bits
per step; the number of surviving classes *grows* (about 11 million classes at
`k = 20`).  The published state of the art (min element `> 2^71 ~ 2.36e21`, Barina 2025,
paper figure; no m-cycles with `m <= 91`, Hercher 2023; `K > 1.375e11` odd
elements via Hercher Cor. 29, conditional on `X_0 >= 3*2^69` and discharged by
Barina) rests on continued fractions, verified computation, and -- for the
per-m ceilings -- Baker's theorem; nothing here approaches it.  The exact
re-run of Hercher's ladder at the 2025 bound is `collatz_maxodd/hercher.py`.

## Corrections to `docs/GROUND_TRUTH.md`

The package encodes the **audited** hypotheses, which differ from the doc:

1. **T1 needs no hypothesis at all.**  `4 | 3M + q` holds for every cycle
   maximum, because `S_q(M) <= M` gives `2^b >= 3 + q/M > 3`.  The doc's two
   claimed counterexamples are not counterexamples: `(q=17, {1,5})` has
   `3*5+17 = 32` (`v2 = 5`) and `(q=23, {7,11})` has `3*11+23 = 56` (`v2 = 3`).
   They refute **T2**, not T1.  In fact `M < q` gives the *stronger* conclusion
   `8 | 3M + q`.
2. **`L >= 2` is redundant in T2/T3/T4** once `M > q` is assumed: `M = q` forces
   `L = 1` (since `3q + q = 4q`), and `L = 1` forces `M = q/(2^b - 3) <= q`.
   The hypothesis must be the **strict** `M > q`, though: at `M = q` the cycle is
   the fixed point with `b_1 = 2`, and `2M - q = q` is never divisible by 3, so
   `M >= q` breaks both halves of T2.
3. **T5's `L >= 3` hypothesis is FALSE.**  Counterexample: `q = 37`, cycle
   `53 -> 49 -> 23 -> 53` has `L = 3`, `M = 53 > q = 37`, `y_2 = 49 < M` (no
   wrap) and `b_2 = 3`.  The correct hypothesis is the **size** condition
   `M > 11q/7`, which is sharp: `7M = 11q` admits `b_2 = 3`, and `q = 7, M = 11`
   is exactly that case (the doc blames the wrap; the real cause is
   `11*7 = 77 = (2^3+3)*7`, equality in the exact inequality).
4. **"T4 recurses to higher powers of 3" is misleading.**  With T0 alone the
   3-adic sieve *saturates immediately* at `M = 2, 8 (mod 9)` -- density `2/9` at
   every depth.  Every further 3-adic gain comes from the size bound `y_k <= M`
   (T6), not from T0.  See `surviving_residues_mod3_no_size`.
5. **T6's `M >= 2^68` is wildly over-conservative.**  `floor_rule_threshold(k)`
   computes the true crossover: `1, 1, 9, 7, 86, 23, 22, 82, 62, 381` for
   `k = 1..10`, and `175, 173, 538, 450, 2012, 1219, 17344, 3536, 3219` for
   `k = 11..19`.  Running maximum over `k <= 19`: **17344**, i.e. `< 2^14.1`,
   not `2^68`.  The sequence is not monotone, so nothing is claimed past `k = 19`.
   The `k = 2` value of `1` (i.e. `M >= 2`) is an independent cross-check of T5.

Two further clarifications the doc does not make:

* **The 2-adic (forward) sieve is unconditional**, unlike the 3-adic one.  A
  residue class killed there contains no cycle maximum of *any* size: the kill
  condition is `2^{A_j} < 3^j`, and `x_j 2^{A_j} = 3^j M + d_j` with `d_j > 0`
  gives `x_j > M` outright.  There is no `floor_rule_threshold` analogue for it.
* **`q <= 0` is rejected, not just undocumented.**  Every claim here needs
  `q > 0` (T1 via `2^b >= 3 + q/M > 3`, T5/T6 via `c_k > 0`, T7 via `c_L > 0`,
  the 2-adic sieve via `d_j > 0`), and for `q < 0` the map does not even keep
  positive odds positive (`S_{-7}(1) = -1`).  `check_q` now raises.

One extra elementary observation the doc does not list:

* **T8** (`q = 1`, no hypothesis): `M != 9 (mod 16)`, so `M = 1, 5, 13 (mod 16)`
  and, with T3, `M = 5, 17, 29 (mod 48)`.
  *Proof.* `M = 16s+9` gives `3M+1 = 4(12s+7)`, so `x_1 = 12s+7` exactly, and
  `3x_1+1 = 2(18s+11)`, so `x_2 = 18s+11 > 16s+9 = M`.  Almost certainly folklore.

## Layout

| module | contents |
|---|---|
| `syracuse.py` | `S_q` and `v2`, forward orbits, the full odd-predecessor family `y_b = (2^b n - q)/3`, and the **unique smaller predecessor** (LEMMA-U) |
| `cycles.py` | exhaustive search: `find_cycles(q, bound)` returns **every** cycle with `M <= bound`, with `L`, `M`, `B`, elements, halving vectors |
| `sieve.py` | the residue sieves on `M`: mod 4 / 12 / 36 by name, the general mod `3^k` and mod `2^a` iterations, their CRT combination, and `can_be_max_odd(M, depth)` with a reason string |
| `backtree.py` | the backward tree from a hypothetical `M`, using the **exact** inequality `M(2^{B_k} - 3^k) <= c_k`; symbolic large-`M` mode; prefix counts `N(k)` |
| `cycleeq.py` | the cycle equation, the product identity, `log2 3` continued fractions and convergents, and the implied cycle-length bounds |

## Usage

```console
$ uv run python -m collatz_maxodd            # the full report
$ uv run python -m collatz_maxodd --q-max 499 --bound 20000 --depth 10
$ uv run pytest                              # verifies T0-T8 empirically
```

```python
from collatz_maxodd import find_cycles, can_be_max_odd, surviving_residues_mod3

find_cycles(37, 200)                  # -> the q=37 cycles, e.g. (53, 49, 23)
can_be_max_odd(7, 1).reason           # -> 'forward: x_1 = 11 > M = 7 ... (this is T1 ...)'
surviving_residues_mod3(1, 1)         # -> (9, (2, 8))    == T4, before the mod-4 CRT
```

## Tests

`tests/` does not just unit-test the code; it **verifies the theorems
empirically**:

* every claim T0-T8 is checked against *every* cycle in a census of ~2100 real
  cycles (`q <= 999`, all cycles with `M <= 20000`), with the audited hypotheses
  attached and with the tightness witnesses asserted;
* the documented edge cases (`q=17 {1,5}`, `q=23 {7,11}`, `q=7 M=11 L=2`,
  `q=37 (53,49,23)`) are asserted as the precise reasons hypotheses can or
  cannot be dropped;
* the surviving residue sets and the backward-prefix counts are pinned to
  hard-coded fixtures from the independent audit;
* the residue sieves are cross-checked against **real integers** (exact backward
  DFS and exact forward orbits on 10 000 values of `M` near `10^6`), not against
  more residue arithmetic;
* every public entry point is asserted to reject even `q`, `3 | q` and `q <= 0`;
* the 2-adic kills are asserted to be unconditional by running real orbits from
  the *smallest* members of each dead class, not just large ones;
* the continued-fraction shortcut behind the cycle-length bound is checked
  against exact big-integer brute force over **every** `L` up to 2966
  (`min element = 10^6`) -- if it skipped a smaller admissible `L` the reported
  bound would be an overclaim.

No runtime dependencies beyond the standard library.
