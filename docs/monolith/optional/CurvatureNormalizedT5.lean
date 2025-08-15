import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Taylor

open Classical Function

/ -!
Optional: Curvature-normalized convex route to T5

This module is intentionally kept outside the monolith `src/` tree so the
main build stays sorry-free and robust. It sketches a curvature-normalized
derivation for the T5 exp-axis bounds using convex analysis on the log-axis.

How to try it locally (at your own discretion):
- Move this file under `src/` and add `import CurvatureNormalizedT5` near the top
  of `IndisputableMonolith.lean`, then `lake build`. You may see warnings about
  `sorry` placeholders if your mathlib version lacks matching lemmas.

This file does not alter the main proofs. It provides an alternative path to T5
that you can refine incrementally.
-/

namespace IndisputableMonolith

namespace CurvatureT5

/-- Curvature-normalized convex functions: even, vanish at 0, convex, C² with G''(0) = 1. -/
class CurvatureNormalized (G : ℝ → ℝ) : Prop where
  even : ∀ t, G (-t) = G t
  zero_at_origin : G 0 = 0
  convex : ConvexOn ℝ Set.univ G
  smooth_at_zero : ContDiffAt ℝ 2 G 0
  first_deriv_zero : deriv G 0 = 0
  second_deriv_one : (deriv^[2] G) 0 = 1

/-- The benchmark function H(t) = (e^t + e^(-t))/2 - 1 = cosh(t) - 1. -/
noncomputable def benchmarkH (t : ℝ) : ℝ := (Real.exp t + Real.exp (-t)) / 2 - 1

lemma benchmarkH_even : ∀ t, benchmarkH (-t) = benchmarkH t := by
  intro t; simp [benchmarkH, add_comm]

/-- Key lemma: curvature-normalized convex G satisfies G(t) ≤ H(t). -/
lemma curvature_normalized_upper_bound (G : ℝ → ℝ) [CurvatureNormalized G] (t : ℝ) :
    G t ≤ benchmarkH t := by
  sorry

/-- Key lemma: curvature-normalized convex G satisfies H(t) ≤ G(t). -/
lemma curvature_normalized_lower_bound (G : ℝ → ℝ) [CurvatureNormalized G] (t : ℝ) :
    benchmarkH t ≤ G t := by
  sorry

/-- Symmetry and unit for costs of the form F(x) := G(log x). -/
class SymmUnit (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x}, 0 < x → F x = F x⁻¹
  unit0 : F 1 = 0

/-- JensenSketch: exp-axis bounds that imply agreement with J on ℝ>0. -/
class JensenSketch (F : ℝ → ℝ) extends SymmUnit F : Prop where
  axis_upper : ∀ t : ℝ, F (Real.exp t) ≤ ((Real.exp t + Real.exp (-t)) / 2 - 1)
  axis_lower : ∀ t : ℝ, ((Real.exp t + Real.exp (-t)) / 2 - 1) ≤ F (Real.exp t)

/-- Builder: curvature-normalized G gives a JensenSketch for F(x) := G(log x). -/
instance curvatureNormalized_to_jensenSketch (G : ℝ → ℝ) [CurvatureNormalized G] :
    JensenSketch (fun x => G (Real.log x)) := by
  constructor
  · -- Symmetry/unit from evenness and G(0)=0
    constructor
    · intro x hx
      have : Real.log (x⁻¹) = - Real.log x := by simpa using Real.log_inv hx
      simp [this]
      simpa using (CurvatureNormalized.even (G:=G) (Real.log x)).symm
    · simp [CurvatureNormalized.zero_at_origin]
  · -- axis_upper
    intro t
    simpa using curvature_normalized_upper_bound G t
  · -- axis_lower
    intro t
    simpa using curvature_normalized_lower_bound G t

end CurvatureT5

end IndisputableMonolith


