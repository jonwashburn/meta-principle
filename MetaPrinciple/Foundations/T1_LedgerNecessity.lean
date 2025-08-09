import MetaPrinciple.Recognition.Ledger.Core

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
  -- Simple witness: constant debit of 1 and zero credit ensures `de` holds: 1 - 0 = 1 = δ
  let L : Ledger M ℝ := {
    delta := 1
  , delta_pos := by norm_num
  , debit := fun _ => 1
  , credit := fun _ => 0
  , de := by intro _ _ _; simp
  }
  exact ⟨L, by simpa using L.delta_pos⟩

end MetaPrinciple
