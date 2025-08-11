/-
Test Harness for Recognition Science
Verifies key numerical values and theorem applications.
-/

import RS.Core
import RS.Hypercube
import RS.GapSeries

namespace RS.Tests

open RS RS.Hypercube RS.GapSeries

/-! ## Numerical Checks -/

/-- J(2) = 5/4 = 1.25 -/
example : J 2 = 5/4 := by
  unfold J
  norm_num

/-- J(1/2) = 5/4 (by symmetry) -/
example : J (1/2) = 5/4 := by
  rw [J_symm (by norm_num : (0 : ℝ) < 1/2)]
  unfold J
  norm_num

/-- φ ≈ 1.618... -/
example : 1.6 < φ ∧ φ < 1.62 := by
  unfold φ
  constructor <;> norm_num

/-- φ² = φ + 1 -/
example : φ * φ = φ + 1 := by
  have h := φ_fixed_point
  field_simp [φ_pos.ne'] at h ⊢
  linarith

/-- The Gray walk has period 8. -/
example : grayWalk.T = 8 := rfl

/-! ## Theorem Applications -/

section Applications

variable {M : RecognitionStructure}

/-- Any ledger has unique structure up to isomorphism. -/
example : ∃ (L : Ledger M), ∀ L', LedgerIso L L' :=
  ledger_necessity_unique M

/-- J is the unique admissible cost functional. -/
example (F : ℝ → ℝ) (hF : AdmissibleCost F) (x : ℝ) (hx : 0 < x) :
  F x = J x :=
  unique_cost_functional hF hx

/-- k must equal 1 for any admissible cost. -/
example (F : ℝ → ℝ) (hF : AdmissibleCost F) (k : ℕ) (hk : k ≥ 1) :
  k = 1 :=
  k_eq_one hF hk

/-- The eight-tick walk is minimal. -/
example (w : EightTick.Walk) : w.T = 8 :=
  eight_tick_minimal w

end Applications

/-! ## Sanity Checks for Core Types -/

#check RecognitionStructure
#check Ledger
#check AdmissibleCost
#check J
#check φ
#check EightTick.Walk
#check gapCoeff

/-- All core axioms that need proofs. -/
#print axioms ledger_necessity_unique
#print axioms unique_cost_functional
#print axioms k_eq_one
#print axioms eight_tick_minimal
#print axioms gap_generating_closed_form

end RS.Tests
