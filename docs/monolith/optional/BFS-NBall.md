### BFS n-ball cardinality bound (optional module)

This optional note documents a finitary breadth-first-search (BFS) construction that yields a geometric upper bound on the size of graph n-balls when out-degree is bounded by `d`.

### Setup

- A bounded out-degree step structure is given by the typeclass `IndisputableMonolith.BoundedStep α d`, with:
  - `step : α → α → Prop`
  - `neighbors : α → Finset α`
  - `step_iff_mem : step x y ↔ y ∈ neighbors x`
  - `degree_bound_holds : (neighbors x).card ≤ d`
- From this, we induce kinematics `K : Causality.Kinematics α` with `K.step := step`.

### BFS covers and bounds

In `src/Optional/NBall.lean` we define two finitary covers:

- `coverExact n x : Finset α` — exact-n shell via repeated neighbor expansion.
- `ballCover n x : Finset α` — union of exact-k shells for `k ≤ n`.

Key lemmas (all in the namespace `IndisputableMonolith.Optional`):

- `mem_coverExact_of_reachN` — if `y` is reachable in exactly `n` steps from `x`, then `y ∈ coverExact n x`.
- `card_coverExact_le_pow (x) (n)` — `(coverExact n x).card ≤ d^n`.
- `mem_ballCover_of_inBall` — if `y` is within the graph-theoretic n-ball (≤ n steps) of `x`, then `y ∈ ballCover n x`.
- `card_ballCover_le_geom_sum (x) (n)` — `(ballCover n x).card ≤ ∑ k∈range (n+1), d^k`.

Together these give a clean, finitary light-cone bound: the n-ball around `x` is contained in a finite set whose cardinality is at most the geometric sum `∑_{k=0}^n d^k`.

### How to use

```lean
import IndisputableMonolith
import Optional.NBall

open IndisputableMonolith
open IndisputableMonolith.Optional

variable {α : Type} {d : Nat}
variable [DecidableEq α] [IndisputableMonolith.BoundedStep α d]

-- Induced kinematics from the bounded step relation
-- def K : Causality.Kinematics α := Optional.K

example (x y : α) (n : Nat)
  (hin : Causality.inBall (Optional.K : Causality.Kinematics α) x n y) :
  (ballCover n x).card ≤ ∑ k in Finset.range (n+1), d ^ k := by
  -- cardinality bound for the finitary over-approximation of the n-ball
  simpa using card_ballCover_le_geom_sum (x:=x) n

example (x y : α) (n : Nat)
  (hin : Causality.inBall (Optional.K : Causality.Kinematics α) x n y) :
  y ∈ ballCover n x :=
  mem_ballCover_of_inBall (x:=x) (y:=y) hin
```

Notes:

- The proof of `card_coverExact_le_pow` uses the standard union bound on `Finset.bind` plus the out-degree cap `(neighbors x).card ≤ d`.
- The n-ball is handled as a union of shells; summing the per-shell bounds yields the geometric sum.


