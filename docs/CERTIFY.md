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
