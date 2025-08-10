import MetaPrinciple.Recognition.Ledger.Core

namespace MetaPrinciple

/-- A simple schedule assigning, for each natural tick, the unique posted entity. -/
class TickSchedule (M : RecognitionStructure) where
  postOf : Nat → M.U

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

/-- Construct an `AtomicTick` instance from a tick `postOf : Nat → M.U` schedule. -/
noncomputable def scheduleAtomicTick
   {M : RecognitionStructure} {C : Type} [LinearOrderedAddCommGroup C]
   (L : Ledger M C) [TickSchedule M] : AtomicTick M C L :=
{ postedAt := fun t u => u = (TickSchedule.postOf (M:=M) t)
, unique_post := by
    intro t
    refine ⟨TickSchedule.postOf (M:=M) t, rfl, ?uniq⟩
    intro u; constructor <;> intro h
    · exact by simpa [h]
    · simpa [h]
}

/-- Corollary: with a tick schedule, no two postings can share a tick. -/
theorem T2_atomicity_of_schedule
  {M : RecognitionStructure} {C : Type} [LinearOrderedAddCommGroup C]
  (L : Ledger M C) [TickSchedule M]
  : ∀ t u v, (scheduleAtomicTick (M:=M) (C:=C) L).postedAt t u →
              (scheduleAtomicTick (M:=M) (C:=C) L).postedAt t v → u = v := by
  -- use the generic lemma with the constructed instance
  classical
  -- Introduce the instance to use `no_concurrent_postings`
  haveI : AtomicTick M C L := scheduleAtomicTick (M:=M) (C:=C) L
  simpa using (no_concurrent_postings (L := L))

end MetaPrinciple
