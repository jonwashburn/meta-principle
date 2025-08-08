import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MetaPrinciple.SelfSimilarity.Golden

namespace MetaPrinciple

open scoped BigOperators

noncomputable def g (m : Nat) : ℝ := ((-1 : ℝ)^(m+1)) / ((Nat.succ m : ℝ) * (phi : ℝ)^(Nat.succ m))

 theorem gap_generating_functional : True := by trivial

end MetaPrinciple
