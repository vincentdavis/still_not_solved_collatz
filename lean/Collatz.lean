/-
  Collatz — a Mathlib-free formalization of the elementary constraints on the
  largest odd element of a `3n+q` Syracuse cycle.

  Notation follows docs/GROUND_TRUTH.md:  S_q, L, M, B, y_k, b_k, B_k, c_k.

  NOVELTY: none is claimed.  T0, T1, T2, T6 and T7 are standard in the Collatz
  cycle literature (Böhm–Sontacchi 1978, Crandall 1978, Brox 2000, Simons–de
  Weger 2005, Kaneda 2015, Hercher 2023); T3, T4, T5 and T8 are one-line
  corollaries of that folklore.  The contribution here is machine-checked
  certainty and a small reusable `Cycle` API, not new mathematics.

  `Collatz/Repeat.lean` adds the repeat theorem of docs/BALANCE.md (Theorem 4).
  The congruence behind it is classical (Terras 1976, Everett 1977), and so is
  the bound on the smallest member (attributed to Crandall 1978, Eliahou 1993
  and Belaga 2003).  The bound on the other members through their height was
  not found stated in the sources checked.  Whether the combination is new is
  discussed, with hedges, in docs/BALANCE.md section 9; no claim is made here.
-/
import Collatz.Odd
import Collatz.Core
import Collatz.Cycle
import Collatz.Length
import Collatz.Minimum
import Collatz.Reach
import Collatz.Periodic
import Collatz.Halving
import Collatz.Census
import Collatz.QTransfer
import Collatz.Words
import Collatz.Repeat
import Collatz.Pigeonhole
import Collatz.Equivalence
import Collatz.Bridge
import Collatz.Examples
import Collatz.Guards
import Collatz.Audit
import Collatz.Unproved
