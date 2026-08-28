# Why a congruence sieve can never finish

Reproduce with `uv run pytest python/tests/test_padic.py`.

Five separate routes in this project end at the same wall. Each ends by
measuring a density that fails to reach zero. This is the same fact stated
without any analysis, densities, or limits — and with an explicit witness.

## Periodic points are the cycle equation

Run the backward map with a fixed halving pattern `(b₁,…,b_L)` and look for a
fixed point. Telescoping gives exactly one, and it is a rational:

```
y  =  c_L / (2^B − 3^L)
```

That **is** the cycle equation. So the periodic points of the backward map are
precisely the candidate cycles — one per halving pattern — and a genuine cycle is
a periodic point that happens to land on a **positive integer**.

`periodic_point` reproduces all **136** real `3n+q` cycles in the census exactly,
from their halving vectors alone, with 0 mismatches.

## The witness: −1

Take the pattern with every `b_j = 1`. Then `3y = 2y − 1`, so **`y = −1`** — for
every length `L`.

In `Z₃` the number `−1` is `…2222`: every digit of its base-3 expansion is a 2, so
`−1 ≡ 3^k − 1 (mod 3^k)` ends in a 2 at every depth — exactly the residue an odd
`b` requires at every step. So

> the class `−1 (mod 3^k)` survives the backward sieve at **every** depth

verified for `k = 1…12`. Hence `a_k ≥ 1` for all `k` — **provably, with a
witness**. The sieve can never empty.

And `−1` is not a natural number.

## The constant patterns, in full

`y = q/(2^b − 3)`:

| b | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|
| `y` (q=1) | **−1** | **1** | 1/5 | 1/13 | 1/29 |

`b = 2` gives `1` — the trivial cycle, and the **only** constant pattern whose
periodic point is a positive integer (checked for `b ≤ 30`).

## The point

A congruence sieve tests membership in `Z₃`. It cannot see **sign** or
**integrality**. Its limit set is full of 3-adic points like `−1` and `1/5` that
pass every congruence test at every depth and are not natural numbers.

Collatz is the statement that **no periodic point other than 1 lands on a
positive integer** — and that is not a congruence question at all. No amount of
sieving addresses it, which is why all five routes in this project stop in the
same place.

It also explains the shape of the earlier measurements. The surviving set has
box dimension `log₃λ`, somewhere in `[0.87, 0.95]` on the computed range —
**positive**, hence uncountable, hence never empty; and **below 1**, hence
density zero. Both halves of "density zero but nonempty" in one number.

## Prior art

The rational form of a cycle is Böhm & Sontacchi (1978); the 3-adic reading of
the Collatz map is standard (Lagarias' survey). Nothing here is new. It is
recorded because it is the cleanest available answer to the question the rest of
the project keeps running into.
