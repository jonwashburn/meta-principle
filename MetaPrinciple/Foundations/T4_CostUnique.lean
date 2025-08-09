import MetaPrinciple.Cost.Functional
import MetaPrinciple.Cost.Uniqueness
import MetaPrinciple.Cost.AnalyticLaurent

namespace MetaPrinciple

/-- T4 (Uniqueness of the Cost Functional): from Laurent data to canonical form. -/
theorem T4_cost_unique_from_laurent (CF : CostFunctional)
  (LD : LaurentData CF.J) : ∀ {x}, 0 < x → CF.J x = J x :=
  cost_unique_from_laurent CF LD

/-- Corollary: if `CF.J` satisfies log‑convexity/analytic regularity, then the canonical form holds. -/
theorem T4_cost_unique_of_logconvex_analytic (CF : CostFunctional)
  (H : LogConvexAnalytic CF.J) : ∀ {x}, 0 < x → CF.J x = J x := by
  intro x hx
  exact cost_unique_from_laurent CF (laurentData_of_logconvex_analytic H) hx

end MetaPrinciple
