/-
  RS/Hyperbolic/CoshIneq.lean
  Lean 4 + mathlib.  No sorrys.
  Provides Jensen-type inequalities for cosh.
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Data.Real.Abs
import Mathlib.Tactic
import «IndisputableChain».Convex.Ratio

open Set Real

namespace RS

private lemma convexOn_cosh_Ici : ConvexOn ℝ (Ici (0:ℝ)) Real.cosh := by
  -- cosh is convex on ℝ; restriction preserves convexity
  simpa using Real.convexOn_cosh.restrict subset_univ

private lemma strictConvexOn_cosh_Ici : StrictConvexOn ℝ (Ici (0:ℝ)) Real.cosh := by
  -- cosh is strictly convex on ℝ; restriction preserves
  simpa using Real.strictConvexOn_cosh.restrict subset_univ

/-- Jensen inequality for `f(t)=cosh t - 1` on `[0,∞)`, lifted to all real `t` via `|t|`. -/
theorem cosh_avg_ineq {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
  (k : ℝ) * (Real.cosh (t / k) - 1) ≤ Real.cosh t - 1 := by
  -- use ratio monotonicity for f = cosh - 1
  have hconv : ConvexOn ℝ (Ici (0:ℝ)) (fun x => Real.cosh x - 1) :=
    (convexOn_cosh_Ici).sub_const 1
  have h0 : (fun x => Real.cosh x - 1) 0 = 0 := by simp
  -- reduce to |t| ≥ 0
  have htpos : 0 < |t| ∨ t = 0 := by
    by_cases h : t = 0
    · exact Or.inr h
    · exact Or.inl (abs_pos.mpr h)
  cases htpos with
  | inr h => simpa [h] using (by have : (k:ℝ) * (Real.cosh 0 - 1) ≤ Real.cosh 0 - 1 := by simp; exact this)
  | inl hpos =>
    have hkpos : 0 < (k:ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le 0)) hk
    have := RS.ratio_mono_of_convexOn_Ici (f := fun x => Real.cosh x - 1)
                  hconv h0 hpos (by exact div_pos hpos hkpos) (by
                    have hk' : 0 < (k:ℝ) := hkpos
                    have := (le_mul_of_one_le_right (le_of_lt hpos) (by exact_mod_cast hk))
                    -- |t| ≤ k * (|t|/k)
                    have : |t| ≤ (k:ℝ) * (|t| / k) := by
                      have hk0 : (k:ℝ) ≠ 0 := ne_of_gt hkpos
                      field_simp [hk0]
                    simpa [mul_comm, mul_left_comm, mul_assoc] using this)
    -- clean up cosh(|t|)=cosh(t)
    have : (k:ℝ) * (Real.cosh (|t| / k) - 1) ≤ Real.cosh (|t|) - 1 := this
    simpa [Real.cosh_abs, abs_div] using this

/-- Strict version: for `k ≥ 2` and `t ≠ 0`, we have strict inequality. -/
theorem cosh_avg_strict {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : t ≠ 0) :
  (k : ℝ) * (Real.cosh (t / k) - 1) < Real.cosh t - 1 := by
  have ht' : 0 < |t| := abs_pos.mpr ht
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le 1)) hk
  have hstrict := RS.ratio_strict_of_strictConvexOn_Ici
      (f := fun x => Real.cosh x) strictConvexOn_cosh_Ici (by simp) ht' hk
  have : (k:ℝ) * Real.cosh (|t| / k) < Real.cosh (|t|) := by simpa using hstrict
  have : (k:ℝ) * (Real.cosh (|t| / k) - 1) < Real.cosh (|t|) - 1 := by
    have := sub_lt_sub_right this 1
    simpa [mul_sub] using this
  simpa [Real.cosh_abs, abs_div] using this

end RS
