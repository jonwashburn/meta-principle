import Mathlib.Tactic

namespace MetaPrinciple

@[simp] def J (x : ℝ) : ℝ := (x + 1/x)/2
@[simp] def J0 (x : ℝ) : ℝ := J x - 1

structure CostFunctional where
  J        : ℝ → ℝ
  symm     : ∀ {x}, 0 < x → J x = J (1/x)
  norm1    : J 1 = 1
  pos      : ∀ {x}, x ≠ 1 → 0 ≤ J x
  bound    : ∃ K > 0, ∀ {x}, 0 < x → J x ≤ K*(x + 1/x)

theorem cost_unique (CF : CostFunctional) : ∀ {x}, 0 < x → CF.J x = J x := by
  intros; admit

end MetaPrinciple
