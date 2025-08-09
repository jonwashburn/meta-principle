import MetaPrinciple.Conservation.Continuity

namespace MetaPrinciple

/-- T3 (Dual‑Balance ⇒ Local Conservation): chainFlux vanishes on closed chains. -/
theorem T3_continuity
  {M : RecognitionStructure} {C : Type} [LinearOrderedAddCommGroup C]
  (L : Ledger M C) [Conserves L]
  : ∀ ch : Chain M,
      ch.f ⟨0, by decide⟩ = ch.f ⟨ch.n, by exact Nat.lt_of_lt_of_le ch.n.isLt (Nat.le_of_lt_succ ch.n.isLt)⟩ →
      chainFlux L ch = 0 :=
  discrete_continuity (L := L)

end MetaPrinciple


