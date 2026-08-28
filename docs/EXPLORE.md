# Three explorations, and what they returned

Proposed at the end of the code review. Reproduce with:

```bash
uv run python python/tools/gen_explore_data.py
uv run pytest python/tests/test_explore.py
```

**Two of the three refuted the guess that motivated them.** Both guesses were
mine, and both were wrong in ways worth keeping.

---

## 1. Where the over-dispersion lives — *the guess was backwards*

The census reports variance/mean = 4.614 where Poisson would give 1, and about a
third of the excess is explained by exact hits (`2^B − 3^L = q`). I guessed the
rest would sit in the `m ≤ q` cycles: the regime where the `+q` term dominates
and the system is least Collatz-like.

It is the other way round.

| population | mean | variance | var/mean | q with any |
|---|---|---|---|---|
| all | 3.243 | 14.965 | **4.614** | 323 / 333 |
| `m > q` | 0.447 | 4.53 | **10.123** | 42 / 333 |
| `m ≤ q` | 2.796 | 10.169 | **3.637** | 317 / 333 |

`m > q` cycles are *rarer* — only 42 of
333 systems have even one — but far more *clustered*, with
one `q` carrying 23. So the excess concentrates
in the regime that most resembles `q = 1`, not the one least like it. That is
the uncomfortable direction, and it is the opposite of what the guess predicted.

Caveat worth stating: var/mean is not scale-free, and the two populations have
very different means (0.447 against
2.796), so the comparison is suggestive rather
than decisive.

### A side result: the quotient is admissible like `q`

Write `k = (2^B − 3^L)/q`. Then `M·k = S`, so an exact hit is `k = 1` and in
general only about `1/k` of the admissible halving vectors can give an integer.
**`k` is always odd and never divisible by 3** — it inherits `q`'s own
admissibility, because `2^B − 3^L` is odd and never `0 mod 3`. Exact hits
account for 14.1% of all cycles.

The obvious follow-up — that cycle counts should fall like `1/k` — does **not**
show up in the data once you condition on classes that have any cycles at all.
The cycle-rich `q` without exact hits (499, 233, 893) have quotients 13, 7, 11
and still concentrate in one or two `(L, B)` classes. So the residual is still
not explained; it is only better localised.

---

## 2. A certified bound on the tail rate — *Fekete runs the other way*

The death-depth tail rate is bracketed `[0.8958, 0.9465]`, and
deciding it needs `k ≈ 36`. I proposed finite-memory relaxations whose spectral
radii would be rigorous **upper** bounds, turning the coin flip into a one-sided
theorem.

The sequence does not cooperate. Over all `j + k ≤ 24`:

```
a_(j+k) / (a_j a_k)  ranges over [1.5, 18.5927]
```

so `a_k` is **supermultiplicative** and emphatically **not** submultiplicative.
Fekete's lemma therefore gives `lim a_k^(1/k) = sup_k a_k^(1/k)` — every term is
a rigorous **lower** bound, and the route yields no upper bound at all.

The best rigorous lower bound is `a_24^(1/24)/3 = 0.7364`.

**This changes how the bracket should be read.** `[0.8958, 0.9465]`
is not an interval of proof: its upper end is the genuine bound `λ/3` from
`a_k ≤ N_k`, but its lower end is where the fitted models put the rate. The
rigorous bracket is

```
[0.7364, 0.9465]
```

which is much wider. Worth keeping straight.

(Supermultiplicativity is *observed on 24 terms*, not proved.
There is a natural argument behind it — the size cap `2^B ≤ 3^k` is
multiplicative, so two surviving chains ought to splice — but this repository
does not prove it, and the rigorous lower bound above is only as good as that
assumption.)

---

## 3. The Hercher pincer — *this one worked*

`L ≤ |R(O)|` is machine-checked (`Cycle.length_le_reach`). Hercher (2023) proves
any nontrivial Collatz cycle has more than `1.375 × 10¹¹` odd elements. Together:
**a Collatz cycle maximum must have `|R(O)| > 1.375 × 10¹¹`.**

So how big does `|R(M)|` actually get, over the surviving class?

| near | sampled | median | mean | p99 | max |
|---|---|---|---|---|---|
| `10^5` | 667 | 4 | 5.24 | 34 | 64 |
| `10^6` | 667 | 3 | 5.45 | 46 | 117 |
| `10^7` | 667 | 3 | 5.02 | 32 | 76 |
| `10^8` | 667 | 4 | 5.15 | 27 | 106 |
| `10^9` | 667 | 3 | 5.2 | 25 | 110 |
| `10^10` | 667 | 3 | 5.57 | 31 | 289 |

**It does not grow.** The median sits at 3–4 across five orders of magnitude and
the largest value seen anywhere is 289 — about
**475,778,547×** below what a cycle would need.

That is a different *kind* of gap from the Diophantine one. It says a
counterexample must be nine orders of magnitude off a distribution that is
otherwise completely flat in `M`.

**What it is not.** A cycle maximum has `|R(O)| ≥ L` by construction, so this is
the same wall wearing another hat — it measures how atypical a counterexample
must be, not that one cannot exist. And the certificate costs the same as the
depth-based one (identical node counts, measured), so it is not cheaper per
number; what it adds is a bound that composes with a published theorem.
