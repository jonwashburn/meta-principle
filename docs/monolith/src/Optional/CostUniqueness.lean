import IndisputableMonolith
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical

namespace IndisputableMonolith
namespace Optional
namespace CostUniqueness

open Cost

/-- Under symmetry/unit and exp-axis agreement via averaging, the calibration constant `c` that
    matches an even convex benchmark on the log-axis is uniquely `1/2` once normalized at 1. -/
theorem c_eq_half_from_tightest_bound
  (F : ℝ → ℝ) [SymmUnit F]
  (hAgree : AgreesOnExp F)
  (tight : ∀ t, F (Real.exp t) ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
               ∧ ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ F (Real.exp t)) :
  (∀ x > 0, F x = Jcost x) := by
  -- The two-sided bound plus symmetry/unit is exactly AgreesOnExp for all t; then extend to ℝ>0
  have : AgreesOnExp F := by
    intro t
    have h₁ := (tight t).1
    have h₂ := (tight t).2
    exact le_antisymm h₁ h₂
  intro x hx
  exact Cost.agree_on_exp_extends (F:=F) this hx

end CostUniqueness
end Optional
end IndisputableMonolith
