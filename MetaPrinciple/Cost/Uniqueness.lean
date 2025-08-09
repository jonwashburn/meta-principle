import Mathlib.Topology.Algebra.InfiniteSum
import MetaPrinciple.Cost.Functional

namespace MetaPrinciple

open scoped BigOperators

/-- Laurent data for a symmetric analytic cost on ℝ_{>0}:
    J(x) = ∑_{n≥1} c_n (x^n + x^{-n}), with normalization ∑ c_n = 1/2
    and vanishing higher coefficients (n ≥ 2). -/
structure LaurentData (F : ℝ → ℝ) : Prop where
  coeff       : ℕ → ℝ
  summable_at : ∀ x > 0, Summable (fun n => coeff (n+1) * (x^(n+1) + x^(-(n+1))))
  expansion   : ∀ x > 0, F x = ∑' n, coeff (n+1) * (x^(n+1) + x^(-(n+1)))
  norm_half   : (∑' n, coeff (n+1)) = (1/2 : ℝ)
  higher_zero : ∀ n ≥ 2, coeff n = 0

/-- From Laurent data with higher modes zero, the canonical cost follows. -/
theorem cost_unique_from_laurent (CF : CostFunctional)
  (LD : LaurentData CF.J) : ∀ {x}, 0 < x → CF.J x = J x := by
  intro x hx
  classical
  -- Use the Laurent expansion and vanishing higher coefficients
  have hxpos : 0 < x := hx
  have hsum := LD.expansion x hxpos
  -- Split the series: only n=0 term (which corresponds to power 1) survives by `higher_zero`
  -- We show the series equals c₁·(x + 1/x)
  have : CF.J x = LD.coeff 1 * (x + 1/x) := by
    -- Define the term function
    have hs : ∑' n, LD.coeff (n+1) * (x^(n+1) + x^(-(n+1)))
            = LD.coeff 1 * (x + 1/x) + ∑' n, LD.coeff (n+2) * (x^(n+2) + x^(-(n+2))) := by
      -- standard shift of index in a tsum
      simpa [pow_one, one_div] using tsum_eq_add_tsum_ite (f := fun n => LD.coeff (n+1) * (x^(n+1) + x^(-(n+1)))) 0
    -- The tail vanishes since all `coeff (n+2)` are zero by `higher_zero`
    have tail_zero : ∑' n, LD.coeff (n+2) * (x^(n+2) + x^(-(n+2))) = 0 := by
      -- Each term is zero
      have : (fun n => LD.coeff (n+2) * (x^(n+2) + x^(-(n+2)))) = (fun _ => (0 : ℝ)) := by
        funext n
        have h : LD.coeff (n+2) = 0 := by exact LD.higher_zero (n+2) (by omega)
        simp [h]
      simpa [this]
    -- Combine
    simpa [hs, tail_zero] using hsum
  -- Determine c₁ from normalization at x=1: CF.J 1 = 1 = 2 · (∑ coeff) = 2 c₁
  have hnorm : LD.coeff 1 = (1/2 : ℝ) := by
    -- Evaluate expansion at x=1
    have h1exp := LD.expansion 1 (by norm_num : 0 < (1:ℝ))
    have h1sum := LD.norm_half
    -- Left: CF.J 1 = 1 by normalization
    have : CF.J 1 = 1 := CF.norm1
    -- Right: sum over n of coeff(n+1) * (1 + 1) = 2 * ∑ coeff(n+1) = 2 * 1/2 = 1
    have : 1 = ∑' n, LD.coeff (n+1) * (1 + 1) := by
      -- 1 = 2 * (1/2) = 2 * tsum coeff = tsum (2*coeff)
      simpa [two_mul, h1sum] using by
        have : (1 : ℝ) = 2 * (1/2 : ℝ) := by ring
        simpa [this]
    -- From termwise equality we get c₁ = 1/2
    -- More directly: compare coefficients using the tail-zero result
    -- Simpler: note that plugging x=1 into the previous identity gives CF.J 1 = c₁ * (1+1) = 2 c₁
    have : CF.J 1 = LD.coeff 1 * (1 + 1/1) := by
      simpa [one_div] using this.replace_eq (by
        -- Actually we can reuse `this` after substituting x=1 in the derived identity
        trivial)
    -- But CF.J 1 = 1
    have : 1 = LD.coeff 1 * 2 := by simpa [CF.norm1, one_div] using this
    have : LD.coeff 1 = (1/2 : ℝ) := by
      have h2ne : (2:ℝ) ≠ 0 := by norm_num
      exact (eq_div_iff_mul_eq h2ne).mpr (by simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using this)
    simpa using this
  -- Finish
  simpa [J, this, hnorm]

end MetaPrinciple
