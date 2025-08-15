import IndisputableMonolith
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic

open Classical

namespace IndisputableMonolith
namespace Optional

variable {f : ℝ → ℝ} {c a t : ℝ}

/-- Even convex functions attain their minimum at 0. -/
lemma even_convex_min_at_zero
  (hconv : ConvexOn ℝ Set.univ f) (he : Function.Even f) : ∀ x, f 0 ≤ f x := by
  intro x
  have hx : x ∈ (Set.univ : Set ℝ) := by trivial
  have hnx : -x ∈ (Set.univ : Set ℝ) := by trivial
  -- 0 is the midpoint of x and -x
  have hmid : f ((1/2 : ℝ) • x + (1/2 : ℝ) • (-x)) ≤
              (1/2) * f x + (1/2) * f (-x) :=
    hconv.2 hx hnx (by norm_num) (by norm_num) (by norm_num)
  simpa [he x, one_div, inv_two, smul_eq_mul, mul_add, add_comm, add_left_comm,
         add_assoc, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using hmid

/-- If an even convex function is dominated on ℝ by the anchored linear bound `f 0 + c |x|`
    and the bound is tight at some `a > 0`, then it is linear on the nonnegative ray. -/
lemma linear_on_nonneg_of_tight_at
  (hconv : ConvexOn ℝ Set.univ f)
  (he : Function.Even f)
  (hc : ∀ x, f x ≤ f 0 + c * |x|)
  (ha : 0 < a ∧ f a = f 0 + c * a) :
  ∀ {t}, 0 ≤ t → f t = f 0 + c * t := by
  intro t ht
  -- Upper bound is immediate from the hypothesis
  have hup : f t ≤ f 0 + c * t := by
    simpa [abs_of_nonneg ht] using hc t
  -- First, show equality on all s ≥ a
  have step_ge : ∀ {s}, a ≤ s → f s = f 0 + c * s := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans (le_of_lt ha.1) hs
    -- convexity at a as a convex combo of 0 and s
    have hcomb : a = (a / s) • s + (1 - a / s) • 0 := by
      have : (a / s) * s + (1 - a / s) * 0 = a := by
        have hspos : 0 < s := lt_of_le_of_lt (le_of_lt ha.1) hs
        field_simp [hspos.ne']
      simpa [smul_eq_mul, this]
    have hineq :=
      hconv.2 (by trivial) (by trivial)
        (by have := div_nonneg (le_of_lt ha.1) hs0; simpa [smul_eq_mul] using this)
        (by
          have : 0 ≤ 1 - a / s := by
            have hspos : 0 < s := lt_of_le_of_lt (le_of_lt ha.1) hs
            have : a / s ≤ 1 := by
              have := div_le_one_of_le hs (by exact hspos)
              simpa using this
            linarith
          simpa [smul_eq_mul] using this)
        (by
          have : (a / s) + (1 - a / s) = (1 : ℝ) := by ring
          simpa [smul_eq_mul] using this)
    -- Using convexity inequality with the above combination
    have : f a ≤ (a / s) * f s + (1 - a / s) * f 0 := by
      simpa [hcomb, smul_eq_mul] using hineq
    -- plug the tight endpoint at a
    have : f 0 + c * a ≤ (a / s) * f s + (1 - a / s) * f 0 := by simpa [ha.2]
    -- rearrange to get a lower bound on f s
    have hspos : 0 < s := lt_of_le_of_lt (le_of_lt ha.1) hs
    have : c * a ≤ (a / s) * (f s - f 0) := by
      have := this
      have h' : (a / s) * f s + (1 - a / s) * f 0 - f 0 = (a / s) * (f s - f 0) := by ring
      have h'' : f 0 + c * a - f 0 = c * a := by ring
      linarith
    have : f s - f 0 ≥ c * a / (a / s) := by
      have hfac : 0 < a / s := by
        have : 0 < a := ha.1
        exact (div_pos this hspos)
      have := (le_div_iff hfac).2 this
      simpa using this
    -- simplify the right-hand side to `c * s`
    have : f s ≥ f 0 + c * s := by
      have hright : c * a / (a / s) = c * s := by
        have hspos' : s ≠ 0 := ne_of_gt hspos
        field_simp [hspos', mul_comm, mul_left_comm, mul_assoc]
      linarith [this]
    -- combine with the global upper bound to conclude equality
    have hup' : f s ≤ f 0 + c * s := by
      simpa [abs_of_nonneg hs0] using hc s
    exact le_antisymm hup' this
  -- If t ≥ a, done by the step above
  by_cases hta : a ≤ t
  · exact step_ge hta
  -- If 0 ≤ t < a, choose any s > a and interpolate a as a convex combo of t and s
  have hlt : t < a := lt_of_le_of_ne (le_of_not_ge hta) (Ne.symm (ne_of_lt ha.1))
  -- pick s := a + 1 (strictly larger than a)
  let s := a + 1
  have hs : a ≤ s := by have : (0 : ℝ) ≤ 1 := by norm_num; linarith
  have hs0 : 0 ≤ s := le_trans (le_of_lt ha.1) hs
  have hs_eq : f s = f 0 + c * s := step_ge hs
  -- write a = (1 - μ) * t + μ * s with μ = (a - t)/(s - t) ∈ [0,1]
  have hden : s - t ≠ 0 := by linarith
  let μ := (a - t) / (s - t)
  have hμ01 : 0 ≤ μ ∧ μ ≤ 1 := by
    constructor
    · have : 0 ≤ a - t := by linarith
      have : 0 ≤ s - t := by linarith
      exact div_nonneg this this
    · have : a - t ≤ s - t := by linarith
      have : (a - t) / (s - t) ≤ 1 := by
        have hpos : 0 < s - t := by linarith
        exact (div_le_one hpos).2 this
      simpa using this
  have hcomb_at : a = (1 - μ) * t + μ * s := by
    have : (1 - μ) * t + μ * s = t + ((a - t) / (s - t)) * (s - t) := by
      field_simp [μ, hden, mul_comm, mul_left_comm, mul_assoc]
    simpa using this
  -- apply convexity at a using points t and s
  have hineq :=
    hconv.2 (by trivial) (by trivial)
      (by have : 0 ≤ 1 - μ := by linarith [hμ01.2]; simpa [smul_eq_mul])
      (by have : 0 ≤ μ := hμ01.1; simpa [smul_eq_mul])
      (by have : (1 - μ) + μ = (1 : ℝ) := by linarith; simpa [smul_eq_mul] using this)
  have : f a ≤ (1 - μ) * f t + μ * f s := by simpa [hcomb_at, smul_eq_mul] using hineq
  -- plug equalities at a and s to get a lower bound on f t
  have : f 0 + c * a ≤ (1 - μ) * f t + μ * (f 0 + c * s) := by simpa [ha.2, hs_eq] using this
  have : (1 - μ) * (f t - (f 0 + c * t)) ≥ 0 := by
    -- rearrange to isolate (1-μ) * (f t - f0 - c t) ≥ 0
    have hleft : (1 - μ) * f t + μ * (f 0 + c * s) - (f 0 + c * a)
                  = (1 - μ) * (f t - (f 0 + c * t)) := by
      have : (1 - μ) * f 0 + μ * f 0 - f 0 = 0 := by ring
      have : μ * (c * s) - c * a = c * ((μ * s) - a) := by ring
      have hta' : (1 - μ) * t + μ * s = a := by
        simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using hcomb_at
      have : μ * s - a = - (1 - μ) * t := by
        have := congrArg (fun z => z - a) hta'
        ring_nf at this
        linarith
      have : c * (μ * s - a) = - c * (1 - μ) * t := by simpa [this, mul_comm, mul_left_comm, mul_assoc]
      ring
    have := sub_nonneg.mpr this
    -- convert to ≥ 0 inequality
    linarith
  -- since 1 - μ ≥ 0, conclude the bracket is ≥ 0
  have h1μ : 0 ≤ 1 - μ := by linarith [hμ01.2]
  have : f t - (f 0 + c * t) ≥ 0 := by
    by_contra hneg
    have : (1 - μ) * (f t - (f 0 + c * t)) < 0 := by
      have hlt' : f t - (f 0 + c * t) < 0 := lt_of_not_ge hneg
      exact mul_neg_of_pos_of_neg (lt_of_le_of_ne h1μ (by intro h; have := hμ01.2; linarith)) hlt'
    exact (lt_of_le_of_lt this this).false
  have hlow : f t ≥ f 0 + c * t := by linarith
  exact le_antisymm hup hlow

/-- Compact corollary: under the same hypotheses, the function is globally `|x|`-linear. -/
theorem bounded_symmetric_is_linear
  (hconv : ConvexOn ℝ Set.univ f)
  (he : Function.Even f)
  (hc : ∀ x, f x ≤ f 0 + c * |x|)
  (ha : ∃ a > 0, f a = f 0 + c * a) :
  ∀ x, f x = f 0 + c * |x| := by
  classical
  rcases ha with ⟨a, ha_pos, ha_eq⟩
  have hnonneg := linear_on_nonneg_of_tight_at (f:=f) (c:=c)
    hconv he hc ⟨ha_pos, by simpa using ha_eq⟩
  intro x
  by_cases hx : 0 ≤ x
  · simpa [abs_of_nonneg hx] using hnonneg hx
  · have hx' : 0 ≤ -x := by linarith
    have := hnonneg (t:=-x) hx'
    have : f (-x) = f 0 + c * |x| := by simpa [abs_neg] using this
    simpa [he x] using this

end Optional
end IndisputableMonolith

namespace IndisputableMonolith
namespace Optional
namespace CostCorollary

open IndisputableMonolith.Cost

/-- If the log-domain model `G` is even, convex, and globally bounded above by a tight linear
    function `G 0 + c |t|`, then the induced positive-domain cost `F := G ∘ log` is
    `F(x) = G 0 + c |log x|` for all `x > 0`. -/
theorem F_ofLog_linear_on_pos_of_log_linear_bound
  {G : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ G) (he : Function.Even G)
  {c : ℝ}
  (hc : ∀ t : ℝ, G t ≤ G 0 + c * |t|)
  (htight : ∃ a > 0, G a = G 0 + c * a) :
  ∀ {x : ℝ}, 0 < x → F_ofLog G x = G 0 + c * |Real.log x| := by
  intro x hx
  -- Apply the global linearity result to G and substitute t = log x
  have hlin :=
    bounded_symmetric_is_linear (f:=G) (c:=c) (hconv:=hconv) (he:=he) (hc:=hc) (ha:=htight)
  simpa using hlin (x:=Real.log x)

end CostCorollary
end Optional
end IndisputableMonolith
