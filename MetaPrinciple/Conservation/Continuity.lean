import MetaPrinciple.Recognition.Ledger.Core

namespace MetaPrinciple

/-- Discrete continuity: local conservation of ledger cost flow (statement skeleton). -/
 theorem discrete_continuity
   {M : RecognitionStructure} {C : Type} [LinearOrderedAddCommGroup C]
   (L : Ledger M C) [Conserves L]
   : ∀ ch : Chain M,
      ch.f ⟨0, by decide⟩ = ch.f ⟨ch.n, by exact Nat.lt_of_lt_of_le ch.n.isLt (Nat.le_of_lt_succ ch.n.isLt)⟩ →
      chainFlux L ch = 0 := by
   intro ch h
   -- Directly apply conservation
   exact Conserves.conserve (L := L) ch h

end MetaPrinciple
