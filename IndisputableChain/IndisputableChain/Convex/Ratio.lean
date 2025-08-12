/-
  RS/Convex/Ratio.lean
  Lean 4 + mathlib. Provides:
  - ratio_mono_of_convexOn_Ici
  - ratio_strict_of_strictConvexOn_Ici
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic

open Set

namespace RS

/-- If `f` is convex on `[0, ∞)` and `f 0 = 0`, then `x ↦ f x / x` is monotone on `(0, ∞)`.
    Concretely: for `0 < x ≤ y`, we have `f x / x ≤ f y / y`. -/
theorem ratio_mono_of_convexOn_Ici
  {f : ℝ → ℝ}
  (hf : ConvexOn ℝ (Ici (0 : ℝ)) f)
  (h0 : f 0 = 0)
  {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) :
  f x / x ≤ f y / y := by
  -- write x as convex combination of y and 0
  set θ : ℝ := x / y with hθdef
  have hy0 : (y:ℝ) ≠ 0 := ne_of_gt hy
  have hθ0 : 0 ≤ θ := by
    have := div_nonneg (le_of_lt hx) (le_of_lt hy)
    simpa [θ] using this
  have hθ1 : θ ≤ 1 := by
    have := (div_le_iff hy).mpr hxy
    simpa [θ] using this
  have hx' : x = θ * y + (1 - θ) * 0 := by
    field_simp [θ, sub_eq, add_comm, add_left_comm, add_assoc]
  have hxmem : x ∈ Ici (0:ℝ) := le_of_lt hx
  have hymem : y ∈ Ici (0:ℝ) := le_of_lt hy
  -- Jensen on the segment {0,y}
  have hJ := hf.2 hymem (by exact (le_of_lt (by norm_num : (0:ℝ) < 1))) hθ0 (by linarith [hθ1])
  have : f x ≤ θ * f y + (1 - θ) * f 0 := by
    simpa [hx', zero_smul, add_comm, add_left_comm, add_assoc] using hJ
  -- divide both sides by x = θ*y > 0 to get the ratio monotonicity
  have hxpos : 0 < x := hx
  have : f x / x ≤ (θ * f y + (1 - θ) * f 0) / x := by
    exact (div_le_div_of_nonneg_right this (le_of_lt hxpos))
  have hxθ : x = θ * y := by
    have := hx'
    simpa using this
  have := le_trans this (by
    have : (θ * f y + (1 - θ) * f 0) / x ≤ (θ * f y) / x := by
      have : (1 - θ) * f 0 = 0 := by simp [h0]
      simpa [this]
    exact this)
  have hx_ne : (x:ℝ) ≠ 0 := ne_of_gt hxpos
  simpa [hxθ, div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc, mul_div_cancel_left₀ _ hy0] using this

/-- Strict version: if `f` is strictly convex on `[0,∞)` with `f 0 = 0`,
    then for `t > 0` and integer `k ≥ 2`, we have `k * f (t / k) < f t`. -/
theorem ratio_strict_of_strictConvexOn_Ici
  {f : ℝ → ℝ}
  (hf : StrictConvexOn ℝ (Ici (0 : ℝ)) f)
  (h0 : f 0 = 0)
  {t : ℝ} (ht : 0 < t) {k : ℕ} (hk : 2 ≤ k) :
  (k : ℝ) * f (t / k) < f t := by
  -- Jensen with θ = 1/k on segment [0,t]
  have kpos : 0 < (k : ℝ) := by exact_mod_cast lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le 1)) hk
  have θ : ℝ := (1 : ℝ) / k
  have hθ0 : 0 < θ := one_div_pos.mpr kpos
  have hθ1 : θ < 1 := by
    have : (1 : ℝ) < k := by exact_mod_cast lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le 1)) hk
    have : θ < 1 := by
      have : 0 < (k : ℝ) := kpos
      simpa [θ] using (one_div_lt_one_of_pos this).mpr this
    exact this
  have hmem0 : (0 : ℝ) ∈ Ici (0 : ℝ) := le_of_lt (by norm_num)
  have hmemt : t ∈ Ici (0 : ℝ) := le_of_lt ht
  have hstrict := hf.2 hmemt hmem0 (le_of_lt hθ0) (by linarith [hθ1]) (by linarith)
  -- strict Jensen
  have : f (θ * t + (1 - θ) * 0) < θ * f t + (1 - θ) * f 0 := by
    simpa [zero_smul, add_comm, add_left_comm, add_assoc] using hstrict
  -- multiply both sides by k = 1/θ
  have θpos : 0 < θ := hθ0
  have hkθ : (k : ℝ) = 1 / θ := by field_simp [θ]
  have := (mul_lt_mul_of_pos_left this (by simpa [hkθ] : 0 < (k : ℝ)))
  -- simplify
  have : (k : ℝ) * f (θ * t) < f t := by
    simpa [hkθ, h0, mul_add, mul_sub, mul_comm, mul_left_comm, mul_assoc, one_sub] using this
  -- θ * t = t / k
  have : (k : ℝ) * f (t / k) < f t := by
    simpa [θ] using this
  exact this

end RS
