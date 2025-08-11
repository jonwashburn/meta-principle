/-!
Tests and concrete examples for the Meta-Principle framework.
These serve as both validation and documentation for AI agents.
-/

import MetaPrinciple.Recognition.Meta
import MetaPrinciple.Recognition.Ledger.Core
import MetaPrinciple.Foundations.T2_Atomicity
import MetaPrinciple.Foundations.T3_Continuity
import MetaPrinciple.LatticeFree

open MetaPrinciple

namespace MetaPrinciple.Tests

/-! ## Test 1: Meta-Principle holds -/
example : MP := mp_holds

/-! ## Test 2: Concrete tiny recognition structure -/

/-- A minimal 2-node recognition structure for testing. -/
def TinyStructure : RecognitionStructure where
  U := Bool
  recog := fun a b => (a = false ∧ b = true) ∨ (a = true ∧ b = false)
  comp := by
    intro a b c hab hbc
    -- In a 2-cycle, composition returns to start
    cases hab with
    | inl h =>
      cases hbc with
      | inl h' => simp [h.1, h'.2] at *
      | inr h' => exact Or.inl ⟨h.1, h'.2⟩
    | inr h =>
      cases hbc with
      | inl h' => exact Or.inr ⟨h.1, h'.2⟩
      | inr h' => simp [h.1, h'.2] at *

/-- A concrete ledger instance on the tiny structure. -/
def TinyLedger : Ledger TinyStructure ℤ where
  delta := 1
  delta_pos := by norm_num
  debit := fun b => if b then 1 else 0
  credit := fun a => if a then 0 else -1
  de := by
    intro a b hab
    cases hab with
    | inl h => simp [h.1, h.2]
    | inr h => simp [h.1, h.2]; ring

/-- A closed 2-chain in the tiny structure. -/
def ClosedChain : Chain TinyStructure where
  n := 2
  f := fun i => match i with
    | ⟨0, _⟩ => false
    | ⟨1, _⟩ => true
    | ⟨2, _⟩ => false
    | ⟨_, h⟩ => absurd h (by omega)
  ok := by
    intro i
    match i with
    | ⟨0, h⟩ => exact Or.inl ⟨rfl, rfl⟩
    | ⟨1, h⟩ => exact Or.inr ⟨rfl, rfl⟩
    | ⟨k, h⟩ => omega

/-- Verify the closed chain is indeed closed. -/
example : ClosedChain.head = ClosedChain.last := by
  simp [Chain.head, Chain.last, ClosedChain]

/-! ## Test 3: Lattice-independent minimality -/

/-- Eight-tick bound applies to any surjection onto 3-bit patterns. -/
example {T : Nat} (f : Fin T → Pattern 3) (hf : Surjective f) : 8 ≤ T :=
  eight_tick_min f hf

/-- Cannot cover 8 patterns with 7 ticks. -/
example : ¬ ∃ f : Fin 7 → Pattern 3, Surjective f := by
  intro ⟨f, hf⟩
  have : 8 ≤ 7 := eight_tick_min f hf
  omega

/-! ## Test 4: Pattern counting -/

example : Fintype.card (Pattern 3) = 8 := by
  simp [card_pattern]

example : Fintype.card (Pattern 4) = 16 := by
  simp [card_pattern]

/-! ## Test 5: Atomic tick uniqueness -/

/-- Mock atomic tick schedule for testing. -/
instance : AtomicTick TinyStructure ℤ TinyLedger where
  postedAt := fun t u => (t = 0 ∧ u = false) ∨ (t = 1 ∧ u = true)
  unique_post := by
    intro t
    cases t with
    | zero => use false; simp
    | succ n =>
      cases n with
      | zero => use true; simp
      | succ _ => use false; simp

/-- Verify T2 holds for our mock schedule. -/
example : ∀ t u v,
  AtomicTick.postedAt t u →
  AtomicTick.postedAt t v →
  u = v := T2_atomicity TinyLedger

end MetaPrinciple.Tests
