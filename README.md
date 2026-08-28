# Which numbers can be the largest odd element of a Collatz cycle?

A Collatz cycle, if one exists, is a finite loop. A finite set of numbers has a
biggest one. So **every cycle has a largest odd element** — call it `M`. That is
not a conjecture, it is arithmetic.

Being the largest is a strong constraint. `M` has to *fall* on the next step
(nothing in the cycle is bigger), and it has to be *reachable* from something
smaller (its predecessor is also in the cycle, hence also ≤ `M`). Both
directions turn into congruences, and most odd numbers fail one of them.

This repo works out how far that idea goes, checks it numerically, and
machine-checks the core of it in Lean 4.

**Nothing here is new mathematics.** Every claim below is elementary and is
already in the Collatz literature; citations are in the status table. What is
here is a clean statement of the exact hypotheses, an empirical check against
thousands of real cycles, and a Mathlib-free Lean development with zero
`sorry`s.

---

## The answer, for classical Collatz (`q = 1`)

Write the Syracuse map on odd numbers:

    S(n) = (3n + 1) / 2^b,   b = v2(3n + 1) ≥ 1

If `M` is the largest odd element of a Collatz cycle, then:

| constraint | needs `M > 1`? | which claim |
|---|---|---|
| `M ≡ 1 (mod 4)` | no | T1 |
| `M ≢ 9 (mod 16)`, i.e. `M ≡ 1, 5, 13 (mod 16)` | no | T8 |
| `M ≡ 2 (mod 3)` | yes | T2 |
| `M ≡ 5 (mod 12)` | yes | T3 |
| `M ≡ 17 or 29 (mod 36)` | yes | T4 |
| `M ≡ 17, 29, 53, 65, 101, 125 (mod 144)` — 6 of 72 odd classes | yes | T4 + T8 |
| `M ≡ 17, 29, 53, 101 (mod 108)` | needs `M ≥ 3` (`M > 11q/7`) | D2 |
| `M ≡ 101, 125, 161, 233, 269, 317 (mod 324)` | needs `M ≥ 11` (`M > 49q/5`) | D3 |

The trivial cycle `{1}` is the one exception to the `M > 1` rows, and it is
excluded from them by hypothesis, not by accident: `M = 1` is the fixed point.

Pushing the sieve deeper keeps cutting, but slowly, and it provably cannot
finish the job — see [What this does **not** prove](#what-this-does-not-prove).

---

## The seed intuitions, graded

The project started from three informal observations. Two are right, one has
the right conclusion for the wrong reason.

**"7 can't be the largest, because 3·7+1 = 22 → 11 > 7."** ✅ Correct, and it is
exactly T1. `7 ≡ 3 (mod 4)`, so `3·7+1 = 22` is only divisible by 2 once, and
one halving never undoes a tripling. Every `n ≡ 3 (mod 4)` fails this way.

**"To reach 11 you'd need a bigger odd number."** ❌ The reason is wrong.
`S(7) = 11`, and `7 < 11` — 11 is reachable from something smaller. (Pinned as a
Lean guard: `Collatz/Guards.lean` asserts `S 1 7 = 11` twice, through two
independent evaluation paths, precisely so this cannot be quietly forgotten.)
But **11 is still excluded**, by the same rule that excluded 7: `11 ≡ 3 (mod 4)`,
so `3·11+1 = 34` halves once to 17 > 11. Right answer, wrong reason.

**"We only need to look two even hops back."** ✅ Correct for `q = 1`, `M ≥ 2` —
this is T5. But the reason is a *size* inequality, not a cycle-length argument:
the correct general hypothesis is `M > 11q/7`, and it is sharp. An earlier draft
of this repo attributed it to `L ≥ 3`, which is false (see the FALSE rows below).

---

## Status table

Setting throughout: `q` odd, `3 ∤ q`, `q > 0`; `S_q(n) = (3n+q)/2^b` with
`b = v2(3n+q)`; `L` = number of odd elements of the cycle, `M` = largest odd
element, `B` = total halvings, `b_k`/`B_k`/`y_k`/`c_k` as in
[`docs/GROUND_TRUTH.md`](docs/GROUND_TRUTH.md).

Empirical column = an exhaustive census of **2127 real `S_q`-cycles** (every
cycle with `M ≤ 20000` for every admissible `q ≤ 999`); of these 1681 have
`L ≥ 2`, 1482 have `M > q`, 1349 have `M > 11q/7`. Re-run it with
`uv run pytest`.

| id | claim (general `q`) | hypotheses | proof | Lean | empirical | prior art |
|---|---|---|---|---|---|---|
| **T0** | every cycle element is coprime to 3 | none | proved | `Cycle.T0` | 2127/2127 | Kaneda, *Fib. Quart.* 53(2) (2015) 168–174 (verbatim, general `d`); Tao, *Forum Math. Pi* 10 (2022) e12; Brox, *Acta Arith.* 92 (2000) 181–188 |
| **T1** | `M ≡ q (mod 4)`, i.e. `4 ∣ 3M+q` | **none** | proved | `Cycle.T1`, `T1_mod4`, `T1_q1` | 2127/2127 | Brox 2000 ("descending"); Simons & de Weger, *Acta Arith.* 117 (2005) 51–70 (local-max decomposition); Terras, *Acta Arith.* 30 (1976) 241–252 |
| **T1′** | `M < q ⇒ 8 ∣ 3M+q`; `M = q ⇒ v2(3M+q) = 2` exactly | none | proved | not formalized | 312/312, 333/333 | routine |
| **U** | every odd `p > 0` coprime to 3 has **at most one** odd `S_q`-predecessor `< p` | none | proved | `pred_unique`, `Cycle.T2_unique` | 499 500 `(q,p)` pairs, 0 exceptions | folklore ("descendent" of a local max, Brox 2000) |
| **T2** | `b_1 = 1`: the in-cycle predecessor of `M` is `(2M−q)/3`; hence `M ≡ 2q (mod 3)` | `M > q` (**strict**) | proved | `Cycle.T2`, `T2_mod3`, `T2_bb`, `T2_q1` | 1482/1482 | built into Simons–de Weger's increase-run structure; Kaneda 2015 Thm 2.1 |
| **FP** | `L = 1 ⇒ M ≤ q`, so `M > q` already forces `L ≥ 2` | none | proved | `q=1` case: `Cycle.M_ge_three_of_L` | 446/446 fixed points | trivial |
| **T3** | `M ≡ 5q (mod 12)`; `q=1`: `M ≡ 5 (mod 12)` | `M > q` | proved (CRT of T1, T2) | `Cycle.T3_gen`, `T3`, `T3_of_L` | 1482/1482 | not found verbatim; one line from folklore — **do not call it a result** |
| **T4** | `M ≢ 5q (mod 9)`, i.e. `M ≡ 17q or 29q (mod 36)`; `q=1`: `M ≡ 17, 29 (mod 36)` | `M > q` (tight) | proved | `Cycle.T4_mod9`, `T4_base_gen`, `T4_base`, `T4_base_of_L` | 1482/1482 | machinery is Wirsching, *LNM 1681* (1998), predecessor-set congruences; the statement not found verbatim |
| **T5** | second backward hop has `b_2 ≤ 2`; exact form `M(2^{1+b_2} − 9) ≤ (2^{b_2}+3)q` | `M > 11q/7` (**sharp**) | proved | `Cycle.T5_gen`, `T5_bb_gen`, `T5`, `T5'`, `T5_of_L`, `T5_bb` | 1349/1349 | local-max neighbourhood analysis: Steiner (1977), Simons, *Math. Comp.* 74 (2005) 1565–1572 |
| **T6** | `y_k ≤ M ⟺ M(2^{B_k} − 3^k) ≤ c_k` | none (it is an `⟺`) | proved | `Cycle.T6`, `T6_iff`, `closed_form` | 2127/2127 | Kaneda 2015 Thm 2.1 ineq. (2.3); Eliahou, *Discrete Math.* 118 (1993) 45–56; Halbeisen & Hungerbühler, *Acta Arith.* 78 (1997) 227–239 |
| **T7** | cycle equation `M(2^B − 3^L) = c_L > 0`, hence `2^B > 3^L` and `B/L > log₂3` | none | proved | `Cycle.T7_eq`, `T7` | 2127/2127 | **Böhm & Sontacchi**, *Atti Accad. Naz. Lincei* 64 (1978) 260–264 — already Lean-formalised at ccchallenge.org; Crandall, *Math. Comp.* 32 (1978) 1281–1292 |
| **T8** | `q=1`: `M ≢ 9 (mod 16)`, hence `M ≡ 1, 5, 13 (mod 16)`; with T3, `M ≡ 5, 17, 29 (mod 48)` | none (mod-16 half) | proved | `Cycle.T8`, `T8_mod16`, `T3_T8` | real orbits from the **smallest** member of each dead class, so the kill is verified unconditional | almost certainly folklore |
| **D2** | `M > 11q/7 ⇒ M ≡ 17q, 29q, 53q, 101q (mod 108)` | `M > 11q/7` | proved (on paper) | **not formalized** | exhaustive sieve, all odd `M ≤ 2·10⁶` at `q=1` | standard backward-sieve pruning |
| **D3** | `M > 49q/5 ⇒ M ≡ 101q, 125q, 161q, 233q, 269q, 317q (mod 324)` | `M > 49q/5` | proved (on paper) | **not formalized** | same | same |

### FALSE claims, kept as warnings

| | claim | why it is false |
|---|---|---|
| ❌ | `B_k ≤ ⌊k·log₂3⌋` unconditionally | `c_k` grows like `2^{B_k}`, not `O(1)`. Real counterexample: `q=5`, cycle `(49, 19, 31)`, `B_3 = 5 > 4`. Only holds for large `M` — the true crossover is `max ≤ 17344` for `k ≤ 19`, not the `2^68` an earlier draft claimed. |
| ❌ | T5 needs `L ≥ 3` | Counterexample `q=37`, cycle `53 → 49 → 23 → 53`: `L = 3`, `M = 53 > q`, `y_2 = 49 < M` (no wrap), and `b_2 = 3`. 33 such cycles in the census. The real hypothesis is the size bound `M > 11q/7`. |
| ❌ | `M > q` is *required* for T1 | T1 holds with no size hypothesis. The two cycles cited as counterexamples — `q=17 {1,5}` and `q=23 {7,11}` — both *satisfy* T1 (`3·5+17 = 32`, `3·11+23 = 56`). They refute **T2**, not T1. And `M < q` gives the *stronger* conclusion `8 ∣ 3M+q`. |
| ❌ | T2 holds under `M ≥ q` | False exactly at `M = q`, which is the fixed point `3q+q = 4q`: there `b_1 = 2` and `3 ∤ 2M−q`. Under `M ≥ q` the census gives 1482/1815. The hypothesis must be **strict**. |
| ❌ | "T4 recurses to higher powers of 3" (as a uniform statement) | T0 *alone* saturates immediately: the 3-adic sieve without the size bound is `M ≡ 2, 8 (mod 9)` at every depth, density `2/9` forever. Every further gain comes from T6, needs its own threshold `M > C_k·q`, and the chain stops being forced at depth 4 — the prefix `(b₁,b₂,b₃,b₄) = (1,1,1,3)` has `2^{B₄} = 64 < 81 = 3⁴`, so `y₄ ≤ M` imposes nothing there. |

---

## What this does **not** prove

**It does not resolve the Collatz conjecture, and it cannot.** Not "we ran out
of time" — the method has a measurable ceiling.

1. **Every `q = 1` statement above with an `M > 1` hypothesis is vacuous if the
   conjecture is true.** `{1}` is the only known `q = 1` cycle, and it fails
   `M > 1`. These are conditional facts about a hypothetical counterexample.
   The evidence that the derivations are *correct* comes from general `q`, where
   real cycles exist and satisfy every claim (e.g. `q=5`: `{49,31,19}`).

2. **The forward (2-adic) sieve saturates.** Its limiting density is
   `0.2863153965…` of the odd numbers — computed by DP to depth 600, confirmed
   against 400 000 real orbits. That is **1.80 bits, forever**. No depth helps.

3. **The backward (3-adic) sieve never reaches zero.** Density falls by roughly
   a factor 0.82 per depth step over the computed range `k ≤ 20`, while the
   modulus grows by `log₂3 ≈ 1.585` bits per step. At `k = 20` you have spent
   33.3 bits of modulus to buy 9.9 bits of sieve, and the surviving class count
   is *growing*: 10 995 110 classes mod `3^21`. Best combined result: about
   **1 odd number in 3300** survives, at modulus ≈ `2^63`.

4. **It is far weaker than the state of the art.** Published bounds — no
   nontrivial cycle has fewer than 92 circuits (Hercher, *JIS* 26 (2023)
   Art. 23.3.5), fewer than `1.375×10¹¹` odd elements, or a minimum element
   below `2.39×10²¹` (Barina, *J. Supercomputing* 81 (2025) art. 810) — rest on
   Baker's theorem plus weeks of dedicated computation. The elementary Crandall
   squeeze reproduced here gets `L ≥ 72 057 431 991`, which is *weaker*, and the
   test suite asserts the published inequality so that weakness cannot be
   quietly dropped.

5. **The CRT product of the two sieves is a statement about residue classes**,
   not automatically about short cycles: it is a joint constraint on an actual
   cycle only when `L` is large enough that the `k` backward and `j` forward
   elements from `M` are disjoint (`L ≥ k+j+1`). Harmless for hypothetical large
   cycles; not proved for short ones.

**Remaining gap, stated plainly.** A residue sieve on `M` can only ever remove a
set of density < 1. Closing Collatz requires either density → 0 at finite depth
(shown above not to happen here) or a Diophantine input — how close `2^B/3^L`
can get to 1 — which is exactly where Baker's theorem enters the literature and
is entirely absent from this repo.

---

## Repo layout

```
docs/GROUND_TRUTH.md    the audited spec: notation, every claim with its exact
                        hypotheses, the refuted claims, formalization status
docs/DEATH_DEPTH.md     d(M), the depth at which the sieve kills M: its exact
                        tail a_k/3^k, and why that is the cycle problem again
docs/CENSUS.md          the 3n+q cycle census: the heuristic is not calibrated,
                        why, and why that does not transfer to q = 1
docs/CERTIFY.md         intersecting the sieve with the path to 1: three complete
                        tests, and which is actually cheapest
docs/WHY_NOT.md         why a congruence sieve can never finish, with -1 as an
                        explicit witness
docs/STRUCTURE.md       what the maximum tells you: L <= |R(O)|, the slow ascent,
                        and >= 41.5% single halvings
python/                 collatz_maxodd — cycle search, sieves, backward tree,
                        cycle equation, death-depth tail, 3n+q census, certification from
                        either end, 3-adic witness, cycle structure; 221 tests
lean/                   Collatz — Mathlib-free Lean 4 development, 0 sorry,
                        0 axioms beyond propext/Quot.sound, 214 audited decls
web/                    data.json (140 KB) + DATA.md — precomputed visualization
                        data (wheel, backward tree, sieve layers, real cycles,
                        Diophantine table), plus index.html — the published interactive note,
                        generated by build_page.py from page.template.html.
```

## Running the Python side

Requires [uv](https://docs.astral.sh/uv/). No runtime dependencies beyond the
standard library; `pytest` is the only dev dependency.

```console
$ cd python
$ uv run pytest
...
221 passed in 7.73s

$ uv run python -m collatz_maxodd                  # full report
$ uv run python -m collatz_maxodd --q-max 499 --bound 20000 --depth 10
```

The tests are not unit tests of the sieve against itself. Every claim T0–T8 is
checked against the full 2127-cycle census, the residue predictions are
cross-checked against **real integers** (exact backward DFS and exact forward
orbits on 10 000 values of `M` near `10⁶`), the tightness witnesses are asserted
as tests, and the continued-fraction shortcut behind the cycle-length bound is
checked against exact big-integer brute force over every `L` up to 2966.

```python
from collatz_maxodd import find_cycles, can_be_max_odd, surviving_residues_mod3

find_cycles(37, 200)            # -> the q=37 cycles, incl. (53, 49, 23)
can_be_max_odd(7, 1).reason     # -> 'forward: x_1 = 11 > M = 7 ... (this is T1 ...)'
surviving_residues_mod3(1, 1)   # -> (9, (2, 8))   == T4, before the mod-4 CRT
```

## Building the Lean side

Requires `elan`; the toolchain (`leanprover/lean4:v4.33.1`) is pinned in
`lean/lean-toolchain`. **No Mathlib** — `lake-manifest.json` has
`"packages": []`, so a clean build takes seconds, not an hour.

```console
$ cd lean
$ lake build
Build completed successfully (11 jobs).

$ ./check.sh
ALL CHECKS PASSED
```

`lake build` succeeding is **not** evidence of no `sorry` — a `sorry` is only a
warning in Lean. `check.sh` is the real gate, and it has five steps: clean build
with zero warnings, a source scan for unsoundness escape hatches
(`sorry`/`axiom`/`native_decide`/`set_option`/`unsafe`/…), a forced-rebuild
axiom audit (214 declarations: 183 on `[propext, Quot.sound]`, 25 on `[propext]`,
6 on none; no `sorryAx`, no `Classical.choice`), a coverage check that every
named declaration is actually audited, and a Mathlib-free check. It has been
verified to *fail* on four deliberately injected defects, including a
build-passing `sorry`.

The `Cycle q` structure is not merely postulated: `Collatz/Bridge.lean` proves
`Cycle.ofOrbit`, which builds a `Cycle q` from hypotheses mentioning only the
forward map (`n` odd, `iter q L n = n`, `n` maximal, `L` least). So *real cycle ⇒
`Cycle q` ⇒ T0–T8* is machine-checked end to end, and `Cycle.y_ne_of_lt` proves
the `L` listed elements are pairwise distinct, so the structure cannot be
satisfied by a short orbit padded out. Three witnesses are constructed:
`one : Cycle 1` (`{1}`), `two7 : Cycle 7` (`{11,5}`), `three5 : Cycle 5`
(`{49,31,19}`, `L=3`, `M > q`).

---

## Honesty notes

- **No novelty is claimed anywhere.** T0/T1/T2/T6/T7 are squarely published.
  T3/T4/T5/T8 were not found written verbatim, which is the weakest possible
  form of novelty and must not be presented as a result. Cautionary precedent:
  Kaneda's own acknowledgements (*Fib. Quart.* 53(2), p. 174) record that
  Lagarias and a referee told him his Section 2 results were not new; the paper
  ran only on the grounds of proof brevity. That is the realistic best case here.
- **No claim is stated as proved beyond what is actually proved.** The Lean
  development's proved/unproved split is recorded inside the source tree
  (`lean/Collatz/Unproved.lean`), not only in a README.
- Two literature gaps could not be closed: an explicit published
  "`M ≡ 5 (mod 12)` for the maximum", and an explicit published mod-`3^j`
  recursion of the T4 form. Absence of evidence only; both are trivially
  derivable from cited folklore.
