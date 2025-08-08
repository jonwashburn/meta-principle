import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

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

end MetaPrinciple
