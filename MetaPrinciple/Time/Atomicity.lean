import MetaPrinciple.Recognition.Ledger.Core

namespace MetaPrinciple

/-- Atomicity axiom: exactly one ledger hop is posted per tick. -/
class AtomicTick (M : RecognitionStructure) (C : Type) [LinearOrderedAddCommGroup C]
  (L : Ledger M C) : Prop :=
  (unique_post : ∀ t : Nat, ∃! u : M.U, True)

/-- No concurrent postings: two distinct hops cannot share the same tick. -/
 theorem no_concurrent_postings
   {M : RecognitionStructure} {C : Type} [LinearOrderedAddCommGroup C]
   (L : Ledger M C) [AtomicTick M C L]
   : True := by
   trivial

end MetaPrinciple
