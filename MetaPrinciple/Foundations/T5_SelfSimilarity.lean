import MetaPrinciple.SelfSimilarity.Golden
import MetaPrinciple.Cost.Functional

namespace MetaPrinciple

/-- T5 (Self-similarity selects k = 1): For any `x0 ≥ 1` and horizon `n`,
    the cumulative cost along the discrete self-similar recurrence is minimized at `k = 1`. -/
theorem T5_self_similarity_minimizes_k
  {x0 : ℝ} (h0 : 1 ≤ x0) (n : Nat) :
  ∀ {k : Nat}, 1 ≤ k → SigmaCost 1 x0 n ≤ SigmaCost k x0 n := by
  intro k hk
  exact k_optimal_is_one (k := k) hk (x0 := x0) h0 n

/-- Corollary: Any fixed point of `x = 1 + 1/x` with `x > 0` is the golden ratio φ. -/
theorem T5_golden_fixed_point {x : ℝ} (hx : x = 1 + 1/x) (hxpos : 0 < x) : x = phi :=
  golden_fixed_point hx hxpos

end MetaPrinciple


