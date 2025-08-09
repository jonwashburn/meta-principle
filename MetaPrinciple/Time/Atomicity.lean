import MetaPrinciple.Recognition.Ledger.Core

namespace MetaPrinciple

/-- Atomicity axiom: exactly one ledger hop is posted per tick. -/
class AtomicTick (M : RecognitionStructure) (C : Type) [LinearOrderedAddCommGroup C]
  (L : Ledger M C) : Prop :=
  (postedAt    : Nat → M.U → Prop)
  (unique_post : ∀ t : Nat, ∃! u : M.U, postedAt t u)

/-- No concurrent postings: two distinct hops cannot share the same tick. -/
theorem no_concurrent_postings
   {M : RecognitionStructure} {C : Type} [LinearOrderedAddCommGroup C]
   (L : Ledger M C) [AtomicTick M C L]
  : ∀ t u v, (AtomicTick.postedAt t u) → (AtomicTick.postedAt t v) → u = v := by
  intro t u v hu hv
  -- By uniqueness of the posted entity at tick t
  rcases (AtomicTick.unique_post (M:=M) (C:=C) (L:=L) t) with ⟨w, hw, huniq⟩
  have hu' : u = w := by
    exact (huniq u).1 hu
  have hv' : v = w := by
    exact (huniq v).1 hv
  simpa [hu', hv']

end MetaPrinciple
