# Intersecting the sieve with the path to 1

Reproduce with `uv run pytest python/tests/test_certify.py`.

## The idea

The residue sieve gives *necessary* conditions on a cycle maximum `M`. Reaching
1 is something else entirely — a **complete refutation**. Nothing in a nontrivial
cycle ever reaches 1 (`lean/Collatz/Equivalence.lean`: `S 1 1 = 1`, so a 1
anywhere in a chain drags the whole chain down to 1). So:

> `M` reaches 1 ⟹ `M` is not the maximum of any nontrivial cycle.

That is why verifying `n < 2.39×10²¹` settles the cycle question below that
bound. The sieve's role is to decide *which* numbers deserve the expensive
complete test.

## Three complete tests, very unequal in cost

| test | what it does | complete because |
|---|---|---|
| `forward_to_one` | run the orbit until it reaches 1 | cycles never reach 1 |
| `forward_exceeds` | run until the orbit **exceeds** `M` | then `M` isn't the max of its own orbit |
| `backward_depth` | exhaust the backward tree from `M` staying `≤ M` | equivalence theorem — an infinite such chain exists **iff** a cycle does, so the DFS *terminating* is the proof |

Measured over 200 000 odd numbers from `10⁷`, counting work units (orbit steps
for the forward tests, tree nodes for the backward one):

| test | work | speedup |
|---|---|---|
| `forward_to_one` | 11 424 896 | 1.0× |
| `forward_exceeds` | 3 095 678 | 3.7× |
| **`backward_depth`** | **414 293** | **27.6×** |

Two thirds of odd numbers die at backward depth 0 — they are `0 mod 3`, or their
forced predecessor is — which is why the backward direction is so much cheaper.

A cross-check worth noting: `forward_exceeds` disposes of **71.33 %** of the
window immediately, and `1 − 0.2863 = 71.37 %` is exactly the complement of the
2-adic sieve's saturation density, computed independently in
[`DEATH_DEPTH.md`](DEATH_DEPTH.md). Two unrelated computations agreeing to three
digits.

## Adding the sieve back, fairly

The general-purpose `sieve.can_be_max_odd` predicate is *slower* than the
backward test it would be prefiltering — measuring it that way makes the sieve
look useless. That is an artefact of it being a research tool. As any real
implementation would do it — a precomputed residue **table** — it earns its keep:

| table | survivors | total time | vs backward alone |
|---|---|---|---|
| none | 100 % | 0.080 s | 1.0× |
| `3², 2⁴` | 8.33 % | 0.025 s | 3.3× |
| `3³, 2⁶` | 5.56 % | 0.022 s | 3.7× |
| `3⁴, 2⁸` | 2.55 % | 0.017 s | 4.7× |
| `3⁵, 2¹⁰` | 1.77 % | 0.016 s | **5.2×** |

**Combined: about 77× cheaper than the naive forward test.** `certify_range`
implements the stack.

## What this is and isn't

It **is** a genuine constant-factor speedup for the cycle question specifically,
and a clean statement of why the two ideas compose: cheap necessary condition,
then complete test.

It is **not** progress on the conjecture. Every test here is complete only for
one `M` at a time; certifying an infinite range still requires an infinite
amount of work. And it does not help the *convergence* question at all — showing
`M` is not a cycle maximum is far weaker than showing every `n` reaches 1.

The non-vacuity guard matters here: `test_real_cycle_maxima_are_not_eliminated`
checks that the backward test correctly **fails** to refute genuine `3n+q` cycle
maxima (`q=5, M=49`; `q=7, M=11`; `q=37, M=53`; …). A test that refuted those
would be refuting a true statement.

## Prior art

None claimed. Restricting a cycle search by residue is standard practice; the
backward formulation is just the equivalence theorem read as an algorithm. The
measurement is what is recorded here.

---

## Both ends: the minimum, and pairing it with the maximum

Everything above constrains the **maximum**. The minimum obeys an exact mirror
image, derived the same way (`collatz_maxodd/bounds.py`).

Let `m` be the minimum. `S_q(m) ≥ m` forces `2^b ≤ 3 + q/m`. **Assume `m > q`**;
then `3 + q/m < 4`, so `b = 1` — the minimum ascends by a single halving, and
`(3m+q)/2` must land odd, i.e. `3m + q ≡ 2 (mod 4)`. A predecessor `y ≥ m` forces
`2^a ≥ 3 + q/m`, so `a ≥ 2`.

| end | hop in | hop out | residue (q = 1) | needs |
|---|---|---|---|---|
| maximum | 1 halving | ≥ 2 | `M ≡ 1 (mod 4)`, `≡ 5 (mod 12)` | `M > q` |
| minimum | ≥ 2 | 1 halving | `m ≡ 3 (mod 4)`, `≡ 7 or 11 (mod 12)` | `m > q` |

**0 violations** over the 77 primitive cycles in the census that satisfy the
hypothesis.

### The hypothesis `m > q` is load-bearing

The census holds 551 primitive cycles for `q < 600`; 474 have `m ≤ q`, and **197
of those break the mirror outright**. The worst is `q = 541`, whose cycle of
length 90 has minimum `m = 25`:

```
3·25 + 541 = 616 = 2³ · 77          — the minimum leaves by THREE halvings
3 + q/m = 24.6                        — nowhere near < 4
```

For `q = 1` the hypothesis is free: the only cycle with `m = 1` is the trivial
one, so any nontrivial cycle has `m ≥ 3 > q`. In `3n+q` it must be checked. The
same applies to the maximum's `M > q` (see `GROUND_TRUTH.md`, T2/T3/T4).
`can_be_min_odd` documents the hypothesis; `gen_bounds_data.py` now counts the
cycles outside it rather than filtering them away silently.

### Formalized (`lean/Collatz/Minimum.lean`)

This was the last result in the project carrying a recorded Lean blocker —
"`Cycle` carries `hmax` but no `hmin`". It did not need one. `hper` makes the
orbit periodic, so the minimum over one period can be **computed** by structural
recursion (`argMinFrom`) instead of postulated: no new field, no change to any
existing instance, no choice principle.

| Lean name | statement |
|---|---|
| `Cycle.m_le` | `m ≤ y i` for every `i` — the minimality the structure never had |
| `Cycle.min_bb_out` | `q < m` ⟹ the step out of the minimum halves exactly once |
| `Cycle.min_bb_in` | the hop into the minimum halves at least twice (no hypothesis) |
| `Cycle.min_mod4` | `3m + q ≡ 2 (mod 4)`, against T1's `3M + q ≡ 0 (mod 4)` |
| `Cycle.min_mod4'` | `m ≡ q + 2 (mod 4)`, against `T1_mod4`'s `M ≡ q (mod 4)` |
| `Cycle.min_mod12_q1` | `q = 1` ⟹ `m ≡ 7 or 11 (mod 12)` |
| `Cycle.ends_disjoint_q1` | both ends at once: `M ≡ 5`, `m ∈ {7, 11}` (mod 12) |
| `Cycle.min_gt_one_q1` | `q = 1`: the hypothesis `q < m` is free |
| `min_bb_out_needs_hypothesis` | `cycle17` fails the hypothesis and the conclusion |
| `min_bb_out_needs_its_own_hypothesis` | **`cycle37` fails `q < m` while satisfying `q < M`** |
| `min_bb_out_hypothesis_not_necessary` | `cycle7` fails `q < m` and satisfies the conclusion anyway |

The last three rows are the ones worth having, and they say three different
things.

`cycle37 : Cycle 37` is the genuine cycle `29 → 31 → 65 → 29`. Its minimum
`m = 29` is `≤ q = 37`, while its maximum `M = 65` is `> q` — so it satisfies the
hypothesis T2/T3/T4 use at the *top* end and fails the one the mirror needs at
the bottom. Its minimum leaves by `3·29 + 37 = 124 = 2² · 31`, two halvings. So
the mirror does **not** inherit the maximum's hypothesis; it needs its own. 167
census cycles have `m ≤ q < M` like this.

`cycle17` (`5 → 1 → 5`) is the extreme version, `m = 1`. But on its own it proves
less than it looks: it fails `q < M` too, so it cannot tell the two hypotheses
apart. That is why `cycle37` is there.

`cycle7` (`11 → 5 → 11`) supplies the caveat. It has `m = 5 ≤ 7 = q` and its
minimum leaves by a single halving regardless. **`q < m` is sufficient, not
necessary** — the 197 census cycles show the hypothesis cannot be dropped, not
that every cycle lacking it breaks.

Counting convention for that 197: primitive cycles of length `≥ 2` (the default
`min_length=2` of `census.primitive_cycles`) with `q < 600` and maxima below
`40q`. Counting the eight length-1 fixed points as well gives 205 of 559.

A side effect: `pow_le_of_min` and `length_bound` in `Length.lean` took the
minimum as a hypothesis `hm : ∀ i, m ≤ y i`, because when they were written
there was no minimum to hand. `Cycle.pow_le_m` and `Cycle.length_bound_m` now
discharge it.

### The sandwich

From `2^B = ∏(3 + q/x_j)` with `m ≤ x_j ≤ M`, and writing `d = B − L·log₂3 > 0`,
`K = 1/(3 ln 2)`:

```
(3 + q/M)^L ≤ 2^B ≤ (3 + q/m)^L        ⟹        m  ≤  K·q·L / d  ≤  M
```

So a **scale computed from `(q, L, B)` alone must land inside the cycle's range**.
0 violations over the 77 cycles with `m > q`; 8 of the 474 without it fail, so the
linearized form inherits the same hypothesis. `q = 47` illustrates it well: five distinct cycles
share `L = 4, B = 7`, hence one scale `136.95` — and every one of them straddles it.

| q | L | B | min m | scale | max M |
|---|---|---|---|---|---|
| 5 | 3 | 5 | 19 | 29.43 | 49 |
| 5 | 3 | 5 | 23 | 29.43 | 37 |
| 47 | 4 | 7 | 65 | 136.95 | 331 |
| 47 | 4 | 7 | 101 | 136.95 | 175 |

### Certifying from either end

Every cycle has both a minimum and a maximum, so refuting either kills it. That
gives two independent certificates for the same claim, "no cycle lies entirely
below X":

| side | test | complete because |
|---|---|---|
| min | `e(m)` — forward steps until the orbit drops below `m` | a minimum cannot descend |
| max | `d(M)` — exhaust the backward tree | the equivalence theorem |

Over 200 000 odd numbers from `10⁷`: min side **698 192** work units, max side
**414 293** — the **max side is 1.7× cheaper**. Exactly half of all odd numbers
are refuted as minima in a single step, which is precisely the `m ≡ 1 (mod 4)`
half that descends — the min test and the residue rule agreeing exactly.

### Does the pairing rule out pairs?

No — and it is worth being clear why. Combining `m ≤ K·q·L/d ≤ M` with the
verified range `m > 2.39×10²¹` gives

```
d  ≤  K·L / 2.39×10²¹  ≈  2.01×10⁻²² · L
```

i.e. `B/L` must approximate `log₂3` to within about `2×10⁻²²`. That is the same
Diophantine wall as everywhere else on this page, reached from a new direction.
The pairing packages the obstruction more symmetrically; it does not weaken it.

---

## Certifying infinitely many numbers at once

Every test above settles one `M` at a time, so no finite amount of work covers a
range. But `d(M)` has a property that changes this: **above a computable
threshold it depends only on `M mod 3^k`**.

The exact size test on a backward prefix is `M(2^{B_j} − 3^j) ≤ c_j`; the
magnitude-free one is `2^{B_j} ≤ 3^j`. They differ only when `2^{B_j} > 3^j` *and*
`M ≤ c_j/(2^{B_j} − 3^j)`. So above

```
T_k  =  max over j ≤ k, over B with 2^B > 3^j,  of  c_j^max / (2^B − 3^j)
```

the two agree. `c_j` is largest when the early hops are smallest (`b_i = 1` for
`i < j`), giving a closed form — no enumeration:

```
c_j^max  =  q · ( 2^(B−j+1) · (3^(j−1) − 2^(j−1)) + 3^(j−1) )
```

This reproduces the project's independently computed `running_max`
(1, 1, 9, 9, 86, …, 538 at `k = 13`) **exactly**, and unlike that computation it
is fast enough to run to `k = 120`.

> **Certificate.** Fix `k`. If the magnitude-free backward tree from a residue
> `r mod 3^k` dies before depth `k`, then **every** odd `M ≡ r (mod 3^k)` with
> `M > T_k` has `d(M) < k`, hence is not the maximum of a nontrivial cycle.

One finite computation, infinitely many numbers.

| k | modulus | alive (`a_k`) | certified | valid for `M >` |
|---|---|---|---|---|
| 3 | 27 | 3 | 88.9 % | 9 |
| 5 | 243 | 10 | 95.9 % | 86 |
| 7 | 2 187 | 50 | 97.7 % | 86 |
| 9 | 19 683 | 254 | 98.7 % | 86 |
| 24 | 3^24 | 182 840 849 | **99.935 %** | 57 528 |

The alive counts are `a_k` again — reached here by a third independent route,
after the full-period scan and the 3-adic tree DFS.

### Which constraint actually binds

`T_k` grows roughly like `(3/2)^k`, but slowly enough that it is **not** the
limit: `T₁₁₈ = 1.87×10²¹` still sits below the verified bound `2.39×10²¹`, while
`T₁₁₉` exceeds it. So the threshold would permit certification to depth ~118.

What stops us is `a_k`, the cost of computing which classes are dead: `a₂₄` is
already `1.8×10⁸` nodes, and it grows like `2.84^k`. **The binding constraint is
computational, not the threshold.**

### And why it can never finish

`a_k > 0` for every `k` — some class always survives. That is not an accident of
the computation: by the equivalence theorem, certifying *every* class would prove
the conjecture. The coverage rises towards 1 and never reaches it, which is the
same wall in yet another disguise.

