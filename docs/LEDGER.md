# The cycle ledger — balance, pairs, gates, and a SAT box

**Provenance.** A visualization-led pass of 2026-09-23 on four ideas
(`web/ledger.html`, which by the user's decision treats **`3n+1` only** — the
general `q` below is the test harness, not the page): that the `3n+1` ascents
and the halving descents of a cycle must balance; that the largest member must be reached from a smaller one
and the smallest left for a larger one; that each odd `n` can be paired with
its descending sum `(13, 35)`; and that the whole question can be handed to a
SAT solver.  Labels follow the house scheme: **PROVED** (complete proof),
**COMPUTED** (exact, this project), **CITED**.  Nothing in this document is
claimed new; the gates are `docs/GROUND_TRUTH.md` T0–T3 and the
`docs/STRUCTURE.md` mirror, restated in the ledger's vocabulary.  Witnesses:
`python/tests/test_ledger.py` (2 tests), `python/tests/test_satcycles.py`
(25 tests, need `python-sat`: `uv run --with python-sat pytest`).

Setting as everywhere in this repo: `S_q(n) = (3n+q)/2^{v₂(3n+q)}` on odd
`n`, `q` odd with `3 ∤ q`; a cycle has odd members `n₁, …, n_L` (sum `O`),
maximum `M`, minimum `m`, `B` halvings, and even members with sum `E`.

---

## 1. The ledger identity (PROVED)

The odd step `n → 3n+q` *ascends* by `2n+q`.  Each halving `u → u/2`
*descends* by `u/2`.  Write `D(n) = (3n+q) − S_q(n)` for the total descent
that follows `n`; e.g. `q = 1`, `n = 13`: `13 → 40` ascends 27, then
`40 → 20 → 10 → 5` descends `20 + 10 + 5 = 35 = D(13)`, net `−8 = 5 − 13`.

> **Identity.** Around any `S_q`-cycle, `Σᵢ (2nᵢ + q) = Σᵢ D(nᵢ) = E/2`.
> Equivalently **`E = 4·O + 2Lq`**, and the sum of *all* members is
> `5·O + 2Lq`.

*Proof.* `S_q` permutes the members, so `Σ (S_q(nᵢ) − nᵢ) = 0`, i.e.
`Σ (3nᵢ + q) − Σ nᵢ = Σ D(nᵢ)`, which is `Σ (2nᵢ + q) = Σ D(nᵢ)`.  Along the
halving chain from `3nᵢ + q` down to `S_q(nᵢ)` every even number `u` of the
cycle is halved exactly once and contributes `u/2`, so `Σ D(nᵢ) = E/2`. ∎

Checks: `1 → 4 → 2 → 1` gives `6 = 4·1 + 2`; the `3n+5` cycle
`{19, 31, 49}` has even members `62, 98, 152, 76, 38`, sum `426 = 4·99 + 30`.
Census: 2 127 / 2 127 (`test_ledger_identity`).

*What it is not.* The balance is a **consequence** of closing, not an extra
test: on its own it says only `Σ S_q(nᵢ) = Σ nᵢ`, which a multiset can satisfy
without `S_q` permuting it.  It is the one *linear* consequence — the row an
integer program would carry — while closure is the nonlinear part.  Nothing
downstream uses it as a constraint.

## 2. Pairs `(n, D(n))` (structure; PROVED, one line each)

With `x = v₂(3n+q)`: `D(n) = (3n+q)(1 − 2^{−x})`, so the pairs lie on the fan
of lines `D = 3(1 − 2^{−x})·n + (1 − 2^{−x})·q`, slopes
`3/2, 9/4, 21/8, 45/16, … → 3`.  The ascent is the single line `2n + q`.
The signed vertical distance to it is `D(n) − (2n+q) = n − S_q(n)`, so:

* below the ascent line ⟺ rise (`S_q(n) > n`) ⟺ `x = 1` when `n ≥ q`
  (for `x ≥ 2`, `S_q(n) ≤ (3n+q)/4 ≤ n`);
* above ⟺ fall; the `x = 2` line meets the ascent line exactly at `n = q`,
  the fixed point `3q + q = 4q`;
* a cycle is a multiset of points whose signed distances sum to zero — the
  ledger identity again, drawn.

## 3. The gates at both ends (PROVED · CITED from this repo)

*Maximum* — `docs/GROUND_TRUTH.md` T1, T2, T3 (Lean `Cycle.T1`–`T3`):
leaving `M` needs `≥ 2` halvings, so `M ≡ q (mod 4)` (no hypothesis);
entering `M` is a single halving when `M > q`, so `M ≡ 2q (mod 3)`;
together `M ≡ 5q (mod 12)`.  For `q = 1`: `M ≡ 5 (mod 12)`.

*Minimum* — `docs/STRUCTURE.md` "Both ends" (Lean `Minimum.lean`,
`min_bb_out`, `m_step_one`): entering `m` needs `≥ 2` halvings (no
hypothesis: the predecessor is larger); leaving `m` is a single halving when
`m > q`, so `3m + q ≡ 2 (mod 4)`, i.e. `m ≡ q + 2 (mod 4)`; and `3 ∤ m` by T0.
For `q = 1`: `m ≡ 7 or 11 (mod 12)`.  The hypothesis is load-bearing (T2's
mirror image): `q = 17`, cycle `{5, 1}`, has `m = 1 < q` leaving by two
halvings (`3 + 17 = 20`).  Census here: 434 / 434 cycles with `m ≥ q, L ≥ 2`
pass; 1 681 / 1 681 minima are entered by `≥ 2` halvings.

In the ledger's words: the top of a cycle is entered by a rise and left by a
fall, the bottom the other way round; a rise is one halving (a congruence
mod 4) and being landed on at all is a congruence mod 3.  That is the entire
content of the mod-12 gates.  The deeper 3-adic levels (T4, D2, D3, the
sieve of `docs/DEATH_DEPTH.md`) are where the project actually lives.

## 4. The SAT box (COMPUTED)

"There is an `S_q`-cycle with `L` odd members, all below `2^W`" is finite, so
it has a CNF.  `python/collatz_maxodd/satcycles.py` writes it (pure Python;
Tseitin gates with constant folding) and `web/ledger.html` carries the same
encoding in JavaScript, specialised to `q = 1`, with MiniSat (logic-solver
2.0.1) running in the page; there every affordable box (`W ≤ 26`) is unsat
above `L = 1`, as Barina's `2^71` bound says it must be, and the page says so.
The encoder's ability to *find* a cycle can only be tested where cycles exist,
which is why the Python harness keeps general `q`.

**Encoding.** `nᵢ` as `W` bits, `n₀` the maximum; `tᵢ = 3nᵢ + q` as `W+2`
bits through two ripple-carry adders (`nᵢ + (nᵢ ≪ 1)`, then `+ q`; the top
carry is provably 0 for `q < 2^W`); one-hot `y_{i,k}`, `k = 1..W+1`, meaning
`v₂(tᵢ) = k`, with `y_{i,k} ⇒` (low `k` bits of `tᵢ` are 0, bit `k` is 1,
`n_{i+1} = tᵢ ≫ k`), indices mod `L`; `nᵢ` odd; `nᵢ < n₀` strictly for
`i ≥ 1` (fixes the rotation and forbids a shorter cycle traversed twice; with
`L = 1` the models are the fixed points `n(2^b − 3) = q`).  Optional gates:
T1 is one unit clause on bit 1 of `n₀`; T2 is one clause behind a comparator
`n₀ > q`; for `q = 1`, T8 (`M ≢ 9 mod 16`) is one 3-literal clause and the
minimum's mirror `m ≡ 3 (mod 4)` is one clause saying some member other than
`n₀` has bit 1 set (sound for `q = 1`, `L ≥ 2`, where `m ≥ 3 > q`).
Enumeration blocks the value of `n₀` after each model — for fixed `L` the
maximum determines the cycle — so each cycle appears exactly once.

**Correctness.** Sound and complete for the box `(L, W)`: on every instance
tested the models are exactly `find_cycles(q, 2^W − 1)` restricted to length
`L` — `q ∈ {1, 5, 7, 11, 13, 17, 19, 23}`, `W ∈ {8, 12}`, `L ≤ 6`; the two
17-cycles of `3n+5` below `2^12` (`M = 2773, 3397`); the seven 5-cycles of
`3n+13` below `2^12`; gates on and off agree; `q = 1`, `W = 16`, `L ≤ 8`
yields only `{1}`.  Every model is re-verified arithmetically before it is
reported.

| box `(q, L, W)` | variables | clauses | result (CaDiCaL via python-sat) |
|---|---|---|---|
| `(5, 3, 8)` | 262 | 1 400 | 2 cycles, `M = 37, 49` |
| `(1, 8, 20)` | 1 862 | 14 568 | unsat |
| `(5, 17, 12)` | 2 386 | 14 508 | 2 cycles, 0.04 s |
| `(1, 12, 24)` | 3 382 | 29 216 | unsat, 8.8 s |
| `(1, 20, 32)` | 7 574 | 77 952 | (size only) |

**Observation (2-adic vs 3-adic).** Every 2-adic gate is *local in binary* —
a clause on the low bits of `n₀` — and the solver gets it by unit propagation.
Every 3-adic gate (T0, the mod-3 half of T2, T4, D2/D3, the whole sieve)
needs a residue circuit per member.  A bit-level encoding therefore sees the
2-adic half of the problem for free and pays for the 3-adic half; the
project's actual content (the 3-adic sieve, `docs/DEATH_DEPTH.md`) is
exactly what the encoding cannot express as clauses.

**3-adic gates as circuits (`gates3 = d`).** `residue_automaton` computes
`n mod 3^k` with a one-hot automaton reading the `W` bits from the top
(`s → (2s + bit) mod 3^k`; `3^k` states per bit position, two 3-literal
transition clauses per state, a sequential at-most-one).  With it the encoder
adds T0 on every member (final state `≠ 0 mod 3`, unconditional) and, on
`n₀`, the survivor sets of `sieve.surviving_residues_mod3` at depths
`1..d` — `{2, 8}` mod 9 (T2 + T4), `{2, 17, 20, 26}` mod 27 (D2), six classes
mod 81 (D3), 13 mod 243, 22 mod 729 — each behind its magnitude threshold so
the box stays exact: `M > q`, `M > 11q/7`, `M > 49q/5` at depths 1–3 for any
`q`, and for `q = 1` `M > floor_rule_safe_M(d) = 1, 1, 9, 9, 86, …` beyond
(deeper gates are offered for `q = 1` only, where those thresholds were
computed).  Checks: the automaton is exact (every residue class mod 3, 9, 27
of the 7-bit numbers enumerated and compared); on the census boxes the 3-adic
gates change nothing, as theorems must (eight boxes with cycles, incl. the
17-cycles of `3n+5` and the 18-cycle of `3n+17`); the gate-only instance
`encode_max_only` enumerates exactly the odd numbers the arithmetic filter
accepts.  Cost, `q = 1`, `W = 16`, `L = 6`: 7 739 clauses without, 15 290 at
depth 3, 67 906 at depth 5 (`≈ 5·3^{d+1}·W` per depth); the ladder `L ≤ 6`
stays unsat above `L = 1`.  What the gates alone leave: below `2^16`, 369 of
the 32 768 odd numbers (1.1 %) pass as candidate maxima; below `2^12`, 22 —
`1, 161, 449, 485, 593, 917, 1133, 1397, 1457, 1853, 1937, 2177, …`.  None
of it changes a verdict; it shows the price of the 3-adic half.

**Verdict.** Inside a box the encoding settles everything; outside it,
nothing.  A nontrivial `3n+1` cycle has `> 1.375×10¹¹` odd members (Hercher
2023, Cor. 29, made unconditional by Barina 2025, both cited in
`docs/GROUND_TRUTH.md` T7) and minimum `> 2^71`; the box that could matter
has `L > 10¹¹`, `W > 71`, about `10¹⁴` clauses, and "unsat" for every smaller
box is already known from the Diophantine bounds — bounded model checking
never closes an unbounded question.  Where SAT has actually contributed is
the other direction: Yolcu, Aaronson & Heule, *An Automated Approach to the
Collatz Conjecture* (CADE-28, 2021; *J. Automated Reasoning*, 2023,
doi:10.1007/s10817-022-09658-8) encode the conjecture as termination of a
string-rewriting system and use SAT to search for termination
*certificates* (matrix interpretations); this proved nontrivial weakenings,
not Collatz.  A SAT approach with any life in it searches for an inductive
invariant, not for a cycle.

## 5. What is checked where

| claim | Python | Lean |
|---|---|---|
| ledger identity `E = 4O + 2Lq`, 2 127 cycles | ✓ `test_ledger.py` | ✗ (not formalized; one line) |
| minimum entered by `≥ 2` halvings; `m ≥ q, L ≥ 2 ⇒` one halving out, `m ≡ q+2 (mod 4)` | ✓ `test_ledger.py` (434 / 1 681) | ✓ `Minimum.lean` (`min_bb_out`, `m_step_one`, hypothesis `q < m`) |
| SAT box = `find_cycles` on every tested box; residue automaton exact; 3-adic gates inert on cycle boxes; gate-only instance = arithmetic filter | ✓ `test_satcycles.py` (25, needs python-sat) | ✗ (computation) |
| in-page: MiniSat models = exhaustive search of the same box, census gates for `q ≤ 199`, `M ≤ 4000` | ✓ `web/ledger.html` (live) | — |

## 6. The multiplicative ledger (`web/multiplicative.html`; PROVED · CITED · COMPUTED)

The additive balance, written multiplicatively.  One odd step with `x`
halvings is `2^x·n′ = 3n + 1 = n·(3 + 1/n)`; multiplied around a cycle the
members cancel:

> **`2^B = ∏ᵢ (3 + 1/nᵢ)`**, i.e. **`B = L·log₂3 + Σᵢ log₂(1 + 1/(3nᵢ))`**
> (`cycleeq.product_identity`; the log form is checked to 40 digits on the
> census, `test_multiplicative.py`).

Along an open trajectory the same product runs as
`2^{B_k}·n_k/n₀ = ∏_{i<k}(3 + 1/nᵢ)`, so `B_k − k·log₂3 = log₂(n₀/n_k) + c_k`
with `c_k ≥ 0` — the page's first chart.

**Squeeze (Crandall 1978, Eliahou 1993).** Every correction term is positive
(`2^B > 3^L`, T7) and at most the one for the smallest member `m`:
`0 < B/L − log₂3 ≤ δ(m) = log₂(1 + 1/(3m)) < 1/(3m·ln 2)`.  With Barina's
`m > 2^71`, `δ < 2.04×10⁻²²`.  If a length `L` admits such a `B`, the fraction
above `log₂3` with denominator `≤ L` closest to it is at least as close and is
a best upper approximation of `log₂3` — an intermediate fraction of an upper
convergent of `[1; 1, 1, 2, 2, 3, 1, 5, 2, 23, …]`
(`cycleeq.best_upper_approximations`; brute-force checked to denominator
3000).  So the smallest possible `L` is the first denominator in that list
whose fraction is within `δ` of `log₂3` (`cycleeq.smallest_admissible_length`,
320-digit arithmetic):

| members above | `δ` | smallest `L` | `B` | `L + B` |
|---|---|---|---|---|
| `2^40` | `4.37×10⁻¹³` | 10 781 274 | **17 087 915** — Eliahou's 1993 number | 27 869 189 |
| `2^60` | `4.17×10⁻¹⁹` | 397 573 379 | 630 138 897 | 1 027 712 276 |
| `2^68` (Barina 2020) | `1.63×10⁻²¹` | 72 057 431 991 | 114 208 327 604 | 186 265 759 595 |
| `2^71` (Barina 2025, in print; `2075·2^60` gives the same) | `2.04×10⁻²²` | 72 057 431 991 | 114 208 327 604 | 186 265 759 595 |
| `2^100` (hypothetical) | `3.79×10⁻³¹` | 3 332 857 981 044 265 | 5 282 454 920 184 382 | 8 615 312 901 228 647 |

The page recomputes the list and the crossing in exact integer arithmetic
(`log₂3` to 90 decimals, 70 continued-fraction terms, denominators to
`10^34`) with a slider for `k`; the five rows above are pinned by
`test_multiplicative.py`.  Eliahou's published `17 087 915` is the `B` of the
`2^40` row, which is the check that the page is drawing the classical
argument and not a variant.  Hercher 2023 goes further
(`L > 1.375×10¹¹`) with the local-maximum structure and Baker's theorem;
nothing here is new, and the squeeze cannot forbid all lengths because best
approximations of the irrational `log₂3` exist at every scale.
