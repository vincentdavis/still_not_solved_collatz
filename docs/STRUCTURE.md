# What the maximum tells you about the rest of the cycle

Reproduce with `uv run pytest python/tests/test_structure.py`.

Fix `O`, the largest odd element. Three things follow, all elementary, all
checked against every cycle in the `3n+q` census.

## 1. The length is bounded by what `O` can reach

A cycle with maximum `O` lies entirely inside `R(O)` — everything reachable
*backward* from `O` without ever exceeding `O`. So

```
L  ≤  |R(O)|
```

Verified: every census cycle sits inside its own `R(O)`, 0 violations. For `q=1`,
`R(O)` is tiny — over 2 000 odd `O` near `10⁶`, **mean 2.05, median 1**, max 68.

**This is also a better algorithm than the one this project started with.**
Computing `R(O)` with a *visited set* always terminates, because the set is
finite. `certify.backward_depth` enumerates chains instead, so on a genuine cycle
maximum it runs until it hits its cap and returns nothing usable.

Two honest caveats:

- On ordinary inputs it is **not faster** — measured 0.91×, identical work. The
  backward tree usually dies before any value repeats, so the visited set is
  pure overhead.
- Its advantage is *conclusiveness*, not speed. For `q = 5, O = 49`:
  `reachable_set` returns `|R| = 10` in 0.01 ms; `backward_depth` burns its cap
  and returns a non-answer.

## 2. The ascent is slow; the descent need not be

Split the cycle at its extremes. Going forward from the minimum `m` up to `O`,
every step multiplies by `(3 + q/x)/2^b ≤ (3 + q/m)/2`, so

```
L_up  ≥  log(O/m) / log((3 + q/m)/2)          ≈  1.71 · log₂(O/m)
```

0 violations across the census. The descent has **no matching bound** — one large
halving can undo many small climbs, and in **17 of 77** census cycles the maximum
drops to the minimum in a *single step*. The two halves of a cycle are
structurally different objects.

Measured ascent share `L_up/L`: mean **0.611**, ranging 0.167 to 0.938.

## 3. At least 41.5 % of the steps are single halvings

Let `u` count steps with exactly one halving. Since `B = u + Σ_{b≥2} b ≥ u + 2(L−u)`:

```
u  ≥  2L − B
```

Exact, and 0 violations across the census.

For `q = 1` this becomes sharp. The min-max sandwich pins `B/L` into
`[log₂3, log₂(3 + 1/m)]`, which for `m > 2.39×10²¹` is `log₂3` to twenty-two
decimal places. So

```
u/L  ≥  2 − log₂3  =  0.41504…
```

> **At least 41.5 % of the steps in a hypothetical Collatz cycle must be single
> halvings** — that is, at least 41.5 % of its odd elements are `≡ 3 (mod 4)`.

(For general `q` the bound is weaker, because `B/L` is not pinned as tightly —
which is why the census shows cycles with `u/L` as low as 0.200, all of them with
`B/L` well above `log₂3`. The bound is satisfied in every case; it just bites
harder when `q/m` is small.)

## What this does not do

None of it constrains a cycle into non-existence. (1) is only as strong as the
published lower bound on `L` it is compared against; (2) and (3) describe the
shape a cycle must have, not whether one exists. They are structure, not
obstruction.

## Prior art

None claimed. All three are one-line consequences of the same squeeze used
throughout the project.
