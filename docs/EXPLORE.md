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

## 2. A certified bound on the tail rate — *the guess was backwards, and then the other direction turned out to be provable*

The death-depth tail rate is bracketed `[0.896, 0.947]`, and deciding it needs
`k ≈ 36`. I proposed finite-memory relaxations whose spectral radii would be
rigorous **upper** bounds, turning the coin flip into a one-sided theorem.

The sequence does not cooperate in that direction. Over all `j + k ≤ 24`:

```
a_(j+k) / (a_j a_k)  ranges over [1.5000, 18.5927]
```

so `a_k` is **supermultiplicative** and emphatically **not** submultiplicative.
Fekete's lemma therefore runs the other way: it gives a rigorous **lower** bound
and no upper bound at all.

That was where this stopped, as an observation on 24 terms. It is now a theorem.

### `a_(j+k) ≥ a_j · a_k`

Write `S_k ⊆ Z/3^k` for the residues surviving the magnitude-free sieve to depth
`k`, so `a_k = |S_k|`. A halving vector `(b_1,…,b_i)` is *live for `M` at depth
`i`* if every division by 3 is exact and the cap `2^{B_t} ≤ 3^t` holds for all
`t ≤ i`.

**Lemma (locality).** Whether `(b_1,…,b_i)` is live for `M` depends only on
`M mod 3^i`.

*Proof.* The closed form gives `3^t y_t = 2^{B_t} M − c_t`, with `c_t` depending
only on the `b`'s. Exactness at step `t` is a condition on `y_(t−1) mod 3`, which
that identity determines from `M mod 3^t`. The cap does not involve `M`. ∎

So `S_i` is well defined. Now fix `j, k`, and for each `r ∈ S_j` choose the
**lexicographically least** live vector `β(r)`; write `B` for its halving total
and `c` for its constant. For `M ≡ r (mod 3^j)`, put `M = r + 3^j t`; then

```
y_j  =  (2^B M − c)/3^j  =  y_j(r) + 2^B · t
```

and since `gcd(2,3) = 1`, `t ↦ y_j(r) + 2^B t` is a **bijection** of `Z/3^k`.
Define `Φ(r, s) = r + 3^j t` for the unique `t` with `y_j ≡ s (mod 3^k)`.

**Claim A — `Φ(r,s) ∈ S_(j+k)`.** By locality `β(r)` is live for `M = Φ(r,s)` at
depth `j`, landing on `y_j ≡ s`. Since `s ∈ S_k`, some `β'` is live for `s` at
depth `k`, hence by locality live for `y_j`. Concatenate. The caps compose,
which is the crux:

```
2^{B + B'_i}  =  2^B · 2^{B'_i}  ≤  3^j · 3^i  =  3^{j+i}
```

so every cap of the spliced chain holds. ∎

**Claim B — `Φ` is injective.** `Φ(r,s) mod 3^j = r`, so `r` is recovered; the
canonical choice makes `β(r)` a function of `r`; then `y_j` is determined by `M`,
and `s = y_j mod 3^k`. ∎

Hence `a_(j+k) = |S_(j+k)| ≥ |S_j × S_k| = a_j · a_k`. **∎**

The canonical choice is the whole trick, and it is where I expected the argument
to fail — the sieve's state is a *set* of live chains, which is exactly why `a_k`
has no finite transfer matrix. But injectivity only needs *some* function of `r`,
not a canonically meaningful one, and a finite nonempty set always has a least
element. The difficulty that blocks the transfer matrix does not block this.

### Consequence: the limit exists, and the bracket's lower end is a fit

`a_k ≥ 1` (the `−1` witness) and `a_k ≤ 3^k`, so `a_k^(1/k) ∈ [1, 3]`. With
superadditivity of `log a_k`, Fekete gives

```
mu  :=  lim_k a_k^(1/k)   EXISTS   and equals   sup_k a_k^(1/k)
```

so **every** computed term is a rigorous lower bound. (Superadditivity does not
make `a_k^(1/k)` monotone — only the running maximum is guaranteed to improve;
it happens to be monotone through `k = 24`, but that is data.) The best
available is `k = 24`:

```
mu  >=  a_24^(1/24)  =  2.2093        tail rate  =  mu/3  >=  0.7364
```

Combined with the standing upper bound `a_k ≤ N_k` (giving `mu ≤ λ = 2.8395`):

### And the upper end, closed the same afternoon

The first draft of this section labelled the upper end "proved (`a_k ≤ N_k`)",
which was wrong: `μ ≤ λ` *also* needs `lim N_k^(1/k) = λ`, and `GROUND_TRUTH.md`
§5 gets that **empirically**. A review caught it. It turns out to be closable
elementarily, in four steps, with no asymptotics and no Stirling.

1. **`a_k ≤ N_k`.** A live halving vector pins its residue — each step's
   divisibility condition fixes one more 3-adic digit — and every surviving
   residue has at least one. So residues inject into vectors.
2. **`N_k ≤ C(⌊kα⌋, k)`**, `α = log₂3`. A live vector has strictly increasing
   partial sums `1 ≤ B_1 < … < B_k` with `B_k ≤ ⌊kα⌋`. Drop the earlier caps
   and what is left is a `k`-subset of `{1, …, ⌊kα⌋}`.
3. **`C(n,k) ≤ n^n / (k^k (n−k)^(n−k))`.** From `1 = (p+q)^n ≥ C(n,k)p^k q^(n−k)`
   at `p = k/n`. One line.
4. **That bound is increasing in `n`** — its log-derivative is `log(n/(n−k)) > 0`
   — and at the real point `n = kα` it is *exactly* `λ^k`:

```
(kα)^(kα) / (k^k · (k(α−1))^(k(α−1)))  =  [α^α/(α−1)^(α−1)]^k  =  λ^k
```

Since `⌊kα⌋ ≤ kα`, chaining gives **`a_k ≤ N_k ≤ C(⌊kα⌋,k) ≤ λ^k` at every
`k`** — so `a_k^(1/k) ≤ λ`, hence `μ ≤ λ` and rate `≤ λ/3 = 0.9465`.

No limit theorem for `N_k` is needed; the bound is exact at every `k`. Verified
in `backtree.chain_bound_holds` for `k ≤ 60` (and `C(⌊kα⌋,k)/λ^k` sits around
0.02–0.09, so there is real room).

### The bracket, closed

| | rate | status |
|---|---|---|
| lower | **0.7364** | **proved** — supermultiplicativity + Fekete |
| upper | **0.9465** | **proved** — `a_k ≤ λ^k` |
| published bracket | `[0.8958, 0.9465]` | lower end is a **model fit**, and is *not* implied by either bound |

So the rigorous interval is `[0.7364, 0.9465]`, both ends theorems — which is
what the first draft claimed before it had earned it. The quoted `[0.896, 0.947]`
is strictly narrower and its lower end is still where the fitted models sit, not
a bound. Narrowing the rigorous interval to meet it is the open problem.

(If you want the upper end without real numbers at all — the discipline the Lean
side keeps — `λ < 2.84` gives `a_k ≤ 2.84^k` and rate `≤ 0.94667`, rational and
barely weaker.)

`deathdepth.splice` implements `Φ`. `test_explore.py` checks it lands in the
survivors and is injective — including at `(j,k) = (5,6)`, `(6,5)` and `(4,7)`.
That last detail matters: below `j + k = 11` no `M` in the image carries two
live depth-`j` chains, so a *non-canonical* implementation would pass a shallow
test. At `(5,6)` one does — `M = 42443 mod 3^11` has depth-5 chains ending at
both `242` and `485 mod 3^6`, both survivors — so the choice function is tested
where it is actually load-bearing.

**Prior art — no novelty claimed.** This is the textbook Fekete setup for a
concatenation-closed family: the admissible halving vectors are closed under
concatenation (the caps compose by `⌊x⌋ + ⌊y⌋ ≤ ⌊x+y⌋`), the residue map
respects it, and a canonical-representative trick turns a surjection into an
injection from a product. The same shape appears for factor complexity of
concatenation-closed languages, and these objects — counts of admissible
vectors, 3-adic classes in the backward tree — are the territory of
Applegate & Lagarias, *Density bounds for the 3x+1 problem I* (Math. Comp. 64,
1995) and Wirsching (LNM 1681). It is half a page of standard argument and is
very likely folklore there. It is written out because the repository was
relying on it as an observation, not because it is new.

*Not formalized in Lean.* The counting step needs "an injection from a product
bounds the product of counts", which the development does not have — the nearest
thing, `Cycle.length_le_count`, uses pigeonhole for a one-sided bound.

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
