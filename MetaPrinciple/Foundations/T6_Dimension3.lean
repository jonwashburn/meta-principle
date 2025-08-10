import MetaPrinciple.Space.Dimension3

namespace MetaPrinciple

/-- T6 (Minimal stable spatial dimension d=3): Under `StableLinking`,
    the minimal dimension supporting stable linking distinctions is `three`. -/
theorem T6_minimal_dimension [StableLinking] : SpatialDim :=
  stable_distinction_dimension

/-- T6 corollary (cost): Hopf link cost has a coherent lower bound for scales `R ≥ 1`. -/
theorem T6_hopf_cost_bound [StableLinking] {R : ℝ} (hR : 1 ≤ R) :
  1 ≤ HopfLinkCost R :=
  hopf_link_cost_lower_bound (R := R) hR

end MetaPrinciple
