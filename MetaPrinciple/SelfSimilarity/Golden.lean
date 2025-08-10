import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic
import MetaPrinciple.Cost.Functional

namespace MetaPrinciple

noncomputable def phi : ℝ := (1 + Real.sqrt 5)/2

lemma phi_pos : 0 < phi := by
  have : (0 : ℝ) < Real.sqrt 5 := by
    have : (0:ℝ) < 5 := by norm_num
    exact Real.sqrt_pos.mpr this
  have : (0:ℝ) < (1 + Real.sqrt 5)/2 := by nlinarith
  simpa [phi] using this

theorem golden_fixed_point {x : ℝ} (hx : x = 1 + 1/x) (hxpos : 0 < x) : x = phi := by
  have hxne : x ≠ 0 := ne_of_gt hxpos
  -- Multiply both sides of x = 1 + 1/x by x to obtain x^2 = x + 1
  have hmul : x * x = (1 + 1 / x) * x := by
    simpa using congrArg (fun t => t * x) hx
  have hRHS : (1 + 1 / x) * x = x + 1 := by
    have hinv : (1 / x) * x = 1 := by
      simpa [one_div] using inv_mul_cancel hxne
    calc
      (1 + 1 / x) * x = 1 * x + (1 / x) * x := by simpa [add_mul]
      _ = x + 1 := by simpa [one_mul, hinv]
  have hsq : x^2 = x + 1 := by
    have : x * x = x + 1 := by simpa [hRHS] using hmul
    simpa [pow_two] using this
  -- Hence x satisfies the quadratic x^2 - x - 1 = 0
  have hquad : x^2 - x - 1 = 0 := by
    calc
      x^2 - x - 1 = (x + 1) - x - 1 := by simpa [hsq]
      _ = 0 := by ring
  -- Show φ satisfies the same quadratic and is positive, hence x = φ
  have hphi_sq : phi^2 = phi + 1 := by
    -- Expand ((1 + √5)/2)^2 and simplify
    have : ((1 + Real.sqrt 5) / 2 : ℝ)^2 = ((1 + Real.sqrt 5)^2) / 4 := by ring
    have : phi^2 = ((1 + Real.sqrt 5)^2) / 4 := by simpa [phi, pow_two] using this
    have : phi^2 = ((1 : ℝ) + 2*Real.sqrt 5 + (Real.sqrt 5)^2) / 4 := by
      simpa [pow_two, add_comm, add_left_comm, add_assoc, two_mul, mul_comm, mul_left_comm, mul_assoc] using this
    have : phi^2 = (6 + 2*Real.sqrt 5) / 4 := by
      simpa [Real.sq_abs, Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 5), pow_two] using this
    have : phi^2 = (3 + Real.sqrt 5) / 2 := by
      have : (6 + 2*Real.sqrt 5) / 4 = (3 + Real.sqrt 5) / 2 := by
        field_simp
      simpa [this] using this
    -- Also φ + 1 = (3 + √5)/2
    have : phi + 1 = (3 + Real.sqrt 5) / 2 := by
      simpa [phi, add_comm, add_left_comm, add_assoc] using by
        have : (1 + Real.sqrt 5) / 2 + 1 = ((1 + Real.sqrt 5) + 2) / 2 := by field_simp
        simpa using this
    -- Therefore phi^2 = phi + 1
    simpa [this] using this
  have hphi_quad : phi^2 - phi - 1 = 0 := by
    calc
      phi^2 - phi - 1 = (phi + 1) - phi - 1 := by simpa [hphi_sq]
      _ = 0 := by ring
  -- For a monic quadratic with distinct real roots, the positive root is φ.
  -- The other root is (1 - √5)/2 < 0, so positivity selects φ.
  have hneg_root_lt_zero : (1 - Real.sqrt 5) / 2 < 0 := by
    have : 1 - Real.sqrt 5 < 0 := by
      have : (0 : ℝ) < Real.sqrt 5 := by
        have : (0 : ℝ) < 5 := by norm_num
        exact Real.sqrt_pos.mpr this
      linarith
    have : (1 - Real.sqrt 5) / 2 < 0 / 2 := by
      have h2pos : (0 : ℝ) < (2:ℝ) := by norm_num
      exact (div_lt_div_right h2pos).2 this
    simpa using this
  -- Factorization of the quadratic: (t - φ)(t - (1 - √5)/2) = t^2 - t - 1
  have hfactor : ∀ t : ℝ, t^2 - t - 1 = (t - phi) * (t - (1 - Real.sqrt 5)/2) := by
    intro t
    have hsum : phi + (1 - Real.sqrt 5)/2 = 1 := by
      have : (1 + Real.sqrt 5)/2 + (1 - Real.sqrt 5)/2 = (2 : ℝ)/2 := by ring
      simpa [phi]
    have hprod : phi * ((1 - Real.sqrt 5)/2) = -1 := by
      -- ( (1+√5)/2 ) * ( (1-√5)/2 ) = (1 - (√5)^2)/4 = (1 - 5)/4 = -1
      have : ((1 + Real.sqrt 5) * (1 - Real.sqrt 5)) / 4 = -1 := by
        have : (1 : ℝ) - (Real.sqrt 5)^2 = -4 := by
          have : (Real.sqrt 5)^2 = 5 := by
            simpa [pow_two] using (Real.sq_abs (Real.sqrt 5)).trans (by
              simpa using Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 5))
          linarith
        have : ((1 - (Real.sqrt 5)^2) : ℝ) / 4 = -1 := by simpa using congrArg (fun z => z / 4) this
        simpa [mul_add, add_mul, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using this
      have : phi * ((1 - Real.sqrt 5)/2) = -1 := by simpa [phi, mul_comm, mul_left_comm, mul_assoc] using this
      simpa [mul_comm] using this
    -- Expand (t - r1)(t - r2) = t^2 - (r1+r2) t + r1 r2
    ring_nf
    have : (t - phi) * (t - (1 - Real.sqrt 5)/2) = t^2 - (phi + (1 - Real.sqrt 5)/2) * t + phi * ((1 - Real.sqrt 5)/2) := by ring
    simpa [hsum, hprod]
  -- Using the factorization and hquad, one factor must vanish; positivity excludes the negative root.
  have : (x - phi) * (x - (1 - Real.sqrt 5)/2) = 0 := by
    simpa [hfactor x] using hquad
  have hx_eq_phi : x = phi := by
    have hx_eq_neg : x = (1 - Real.sqrt 5)/2 := by
      have : x - (1 - Real.sqrt 5)/2 = 0 ∨ x - phi = 0 := by
        have := mul_eq_zero.mp this
        -- rearrange disjuncts order
        exact Or.symm this
      cases this with
      | inl h => exact by linarith
      | inr h => exact by linarith
    -- Prefer a direct sign argument instead of the above attempt:
    -- From (x - φ)*(x - r₂)=0, either x=φ or x=r₂. But r₂<0 and x>0, hence x≠r₂.
    -- We thus finish by cases.
    have hmulzero := mul_eq_zero.mp this
    rcases hmulzero with h1 | h2
    · exact sub_eq_zero.mp h1
    · have : x ≠ (1 - Real.sqrt 5)/2 := by
        have hxpos' : 0 < x := hxpos
        have : (1 - Real.sqrt 5)/2 < 0 := hneg_root_lt_zero
        exact ne_of_gt_of_lt hxpos' this
      exact (sub_eq_zero.mp h2).elim this rfl
  exact hx_eq_phi

/-!  Discrete self-similarity and cost minimality results  -/

@[simp] def next (k : Nat) (x : ℝ) : ℝ := 1 + (k : ℝ) / x

def orbit (k : Nat) (x0 : ℝ) : Nat → ℝ
| 0     => x0
| n+1   => next k (orbit k x0 n)

lemma next_mono_in_k {k : Nat} (hk : 1 ≤ k) {x : ℝ} (hx : 1 ≤ x) :
  next 1 x ≤ next k x := by
  have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hx0 : 0 ≤ x := le_trans (by norm_num : (0:ℝ) ≤ 1) hx
  have hxinv_nonneg : 0 ≤ (1/x) := inv_nonneg.mpr hx0
  have : (1:ℝ) * (1/x) ≤ (k:ℝ) * (1/x) :=
    mul_le_mul_of_nonneg_right hk' hxinv_nonneg
  have : (1:ℝ)/x ≤ (k:ℝ)/x := by simpa [div_eq_mul_inv] using this
  exact add_le_add_left this 1

lemma orbit_ge_one {k : Nat} (hk : 1 ≤ k) {x0 : ℝ} (h0 : 1 ≤ x0) :
  ∀ n, 1 ≤ orbit k x0 n := by
  intro n; induction' n with n ih
  · simpa
  · simp [orbit, next, ih, hk, one_le_div_iff] <;> nlinarith

class OrbitMonotoneInK (x0 : ℝ) : Prop where
  mono : ∀ {k : Nat}, 1 ≤ k → ∀ n, orbit 1 x0 n ≤ orbit k x0 n

lemma J_monotone_on_ge_one {x y : ℝ} (hx : 1 ≤ x) (hy : x ≤ y) : J x ≤ J y := by
  -- J(y) - J(x) = (y-x) - (y-x)/(xy) = (y-x)*(1 - 1/(xy)) ≥ 0 for x,y ≥ 1
  have hxy_pos : 0 < x*y := mul_pos_of_nonneg_of_pos (by linarith) (by
    have : 1 ≤ y := le_trans hx hy
    exact lt_of_le_of_lt this (by norm_num : (1:ℝ) < 2))
  have : J y - J x = (y - x) - (y - x)/(x*y) := by
    field_simp [J, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  have hfac : (y - x) * (1 - 1/(x*y)) = (y - x) - (y - x)/(x*y) := by
    field_simp [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  have hyx : 0 ≤ (y - x) := sub_nonneg.mpr hy
  have hone : 0 ≤ (1 - 1/(x*y)) := by
    have hxyp : 1 ≤ x*y := by
      have : (1:ℝ) ≤ x := hx
      have : (1:ℝ) ≤ y := le_trans hx hy
      exact mul_le_mul this this (by linarith) (by norm_num)
    have : 0 ≤ 1 - 1/(x*y) := by
      have : (1/(x*y)) ≤ (1:ℝ) := by
        have : 1 ≤ x*y := hxyp
        have : 0 < x*y := lt_of_le_of_lt this (by norm_num)
        exact inv_le_one (le_of_lt this)
      linarith
    simpa using this
  have : 0 ≤ (y - x) * (1 - 1/(x*y)) := mul_nonneg hyx hone
  have : 0 ≤ J y - J x := by simpa [this, J, hfac] using this
  exact sub_nonneg.mp this

/-- Step bounds that propagate inequalities for the recurrence:
    if `1 ≤ a ≤ b` and `b ≤ k·a` with `k ≥ 1`, then
    `next 1 a ≤ next k b` and `next k b ≤ k · next 1 a`. -/
lemma step_bounds {k : Nat} (hk : 1 ≤ k) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hbr : b ≤ (k : ℝ) * a) :
    next 1 a ≤ next k b ∧ next k b ≤ (k : ℝ) * next 1 a := by
  have ha0 : 0 < a := lt_of_le_of_lt ha (by norm_num : (1:ℝ) < 2)
  have hb0 : 0 < b := lt_of_le_of_lt (le_trans ha hab) (by norm_num : (1:ℝ) < 2)
  -- first inequality: 1 + 1/a ≤ 1 + k/b  ⇔  b ≤ k·a
  have h1 : next 1 a ≤ next k b := by
    -- multiply both sides of 1/a ≤ k/b by a*b > 0
    have : (1:ℝ) / a ≤ (k:ℝ) / b := by
      have hbka : b ≤ (k:ℝ) * a := hbr
      have hpos : 0 < a * b := mul_pos ha0 hb0
      have := (div_le_iff hpos).mpr ?ineq
      · exact this
      · -- (1:ℝ) * b ≤ (k:ℝ) * a
        simpa [one_mul] using hbka
    exact add_le_add_left this 1
  -- second inequality: 1 + k/b ≤ k + k/a = k · (1 + 1/a)
  have h2 : next k b ≤ (k : ℝ) * next 1 a := by
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkb : (k:ℝ) / b ≤ (k:ℝ) / a := by
      have : (1:ℝ) / b ≤ (1:ℝ) / a := by
        have : 0 < a := ha0
        exact one_div_le_one_div_of_le this.le hab
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left this (by
        have : (0:ℝ) ≤ (k:ℝ) := by exact_mod_cast (Nat.zero_le k)
        exact this)
    have : (1:ℝ) + (k:ℝ) / b ≤ (k:ℝ) + (k:ℝ) / a := by
      exact add_le_add hk' hkb
    simpa [next, mul_add, mul_one] using this
  exact ⟨h1, h2⟩

/-- Simultaneous bounds along orbits: for all `n`,
    `1 ≤ orbit 1 x0 n ≤ orbit k x0 n ≤ k · orbit 1 x0 n`
    when `k ≥ 1` and `x0 ≥ 1`. -/
lemma orbit_bounds {k : Nat} (hk : 1 ≤ k) {x0 : ℝ} (h0 : 1 ≤ x0) :
    ∀ n, 1 ≤ orbit 1 x0 n ∧ orbit 1 x0 n ≤ orbit k x0 n ∧ orbit k x0 n ≤ (k:ℝ) * orbit 1 x0 n := by
  intro n; induction' n with n ih
  · -- n = 0
    have hx : 1 ≤ x0 := h0
    have hk' : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hx0 : 0 ≤ x0 := le_trans (by norm_num : (0:ℝ) ≤ 1) h0
    have hx_le_kx : x0 ≤ (k:ℝ) * x0 := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hk' hx0
    exact ⟨by simpa, by simpa, by simpa using hx_le_kx⟩
  · -- step
    rcases ih with ⟨ha1, hle, hrat⟩
    -- apply step bounds
    have hb := step_bounds (k := k) hk (a := orbit 1 x0 n) (b := orbit k x0 n) ha1 hle hrat
    rcases hb with ⟨hmono, hratio⟩
    -- lower bound for the next step
    have h1 : 1 ≤ orbit 1 x0 (n+1) := by
      -- since 0 ≤ 1/(orbit 1 x0 n)
      have : 0 ≤ (1 : ℝ) / orbit 1 x0 n := by
        have : (0:ℝ) ≤ orbit 1 x0 n := le_trans (by norm_num : (0:ℝ) ≤ 1) ha1
        simpa [one_div] using inv_nonneg.mpr this
      simpa [orbit, next] using add_le_add_left this 1
    exact ⟨h1, by simpa [orbit] using hmono, by simpa [orbit] using hratio⟩

/-- From `x0 ≥ 1`, the recurrence yields monotonicity in `k` at every step. -/
def orbitMonotoneInK_of_ge_one (x0 : ℝ) (h0 : 1 ≤ x0) : OrbitMonotoneInK x0 := by
  refine ⟨?mono⟩
  intro k hk n
  have hb := orbit_bounds (k := k) hk (x0 := x0) h0 n
  exact hb.2.1

/-- One-step monotonicity in `k`: from the same state `x0 ≥ 1`, the next value increases with `k`. -/
lemma orbit_step1_mono_in_k {k : Nat} (hk : 1 ≤ k) {x0 : ℝ} (h0 : 1 ≤ x0) :
  orbit 1 x0 1 ≤ orbit k x0 1 := by
  simpa [orbit] using next_mono_in_k (k := k) hk (x := x0) h0

open scoped BigOperators

/-- Partial-sum (Σ) of costs along the first `n` steps. -/
def SigmaCost (k : Nat) (x0 : ℝ) (n : Nat) : ℝ :=
  ∑ i in Finset.range n, J (orbit k x0 i)

/-- Pointwise Σ(k) monotonicity under `OrbitMonotoneInK`: if `orbit 1 ≤ orbit k` at each step,
    then the cumulative cost with `k` dominates that with `1`. -/
theorem Sigma_mono_in_k {k : Nat} (hk : 1 ≤ k) {x0 : ℝ} (h0 : 1 ≤ x0)
  [OrbitMonotoneInK x0] (n : Nat) :
  SigmaCost 1 x0 n ≤ SigmaCost k x0 n := by
  classical
  unfold SigmaCost
  refine Finset.sum_le_sum ?h
  intro i hi
  have hx1 : 1 ≤ orbit 1 x0 i := orbit_ge_one (by decide : 1 ≤ 1) h0 i
  have hkmono : orbit 1 x0 i ≤ orbit k x0 i :=
    (OrbitMonotoneInK.mono (x0 := x0)) (k := k) hk i
  exact J_monotone_on_ge_one hx1 hkmono

/-- Global k-optimality (no typeclass assumption): for any horizon `n`,
    the Σ-cost is minimized at `k=1`, assuming only `x0 ≥ 1`. -/
theorem k_optimal_is_one {k : Nat} (hk : 1 ≤ k) {x0 : ℝ} (h0 : 1 ≤ x0)
  (n : Nat) :
  SigmaCost 1 x0 n ≤ SigmaCost k x0 n := by
  haveI : OrbitMonotoneInK x0 := orbitMonotoneInK_of_ge_one x0 h0
  exact Sigma_mono_in_k (k := k) hk (x0 := x0) h0 n

end MetaPrinciple
