import MetaPrinciple.Time.Atomicity

namespace MetaPrinciple

/-- T2 (Atomicity & Countability): no two postings can occur at the same tick. -/
theorem T2_atomicity
  {M : RecognitionStructure} {C : Type} [LinearOrderedAddCommGroup C]
  (L : Ledger M C) [AtomicTick M C L]
  : ∀ t u v, (AtomicTick.postedAt t u) → (AtomicTick.postedAt t v) → u = v :=
  no_concurrent_postings (L := L)

end MetaPrinciple


