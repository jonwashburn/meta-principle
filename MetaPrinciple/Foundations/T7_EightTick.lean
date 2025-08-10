import MetaPrinciple.Time.EightTick

namespace MetaPrinciple

/-- T7 (Eight-tick minimality for D=3): Existence (Gray cycle) and minimality (cardinality). -/
theorem T7_eight_tick :
  (∃ w : RecWalk, True) ∧ (∀ {T : Nat}, T < 8 → ¬ ∃ f : Fin T → V, Surjective f) := by
  constructor
  · exact ⟨{ cycle := gray8, edges := gray8_adj }, trivial⟩
  · intro T hT; exact no_cover_with_period_lt_eight (T := T) hT

/-- T7 generalized: for any `D`, Gray code yields period `2^D` and this is minimal by cardinality.
    Requires an instance providing a D-bit Gray code. -/
theorem T7_hypercube (D : Nat) [HasGrayCode D] :
  (∃ w : RecWalkD D, True) ∧ (∀ {T : Nat}, T < 2 ^ D → ¬ ∃ f : Fin T → VD D, Surjective f) :=
  hypercube_period_exact D

end MetaPrinciple
