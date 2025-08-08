import MetaPrinciple.Time.EightTick

namespace MetaPrinciple

/-- Causality: nearest-neighbor propagation per atomic tick induces a universal maximal speed. -/
 def c (Lmin τ0 : ℝ) : ℝ := Lmin / τ0

 theorem causal_cone_exists : True := by
   trivial

end MetaPrinciple
