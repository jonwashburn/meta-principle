import MetaPrinciple.Recognition.Ledger.Core
import MetaPrinciple.Recognition.Ledger.FreeGroup

namespace MetaPrinciple

/-- T1 (Ledger Necessity & Uniqueness): placeholder existence under finiteness.
    A concrete (but non-unique) positive double-entry ledger over ℝ. -/
structure LedgerExists (M : RecognitionStructure) (C : Type) [LinearOrderedAddCommGroup C] : Prop where
  exists_pos : ∃ (L : Ledger M C), (0 : C) < L.delta

/-- Under `Finiteness`, a positive double-entry ledger exists (uniqueness deferred). -/
theorem T1_ledger_necessity (M : RecognitionStructure) [Finiteness M]
  : ∃ C, ∃ _ : LinearOrderedAddCommGroup C, LedgerExists M C := by
  classical
  refine ⟨ℝ, inferInstance, ?_⟩
  refine ⟨?_⟩
  -- Use the free-group derived ledger as a canonical witness
  let L := ledgerFromFree M
  exact ⟨L, by simpa using L.delta_pos⟩

end MetaPrinciple
