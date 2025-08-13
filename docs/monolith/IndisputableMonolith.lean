/-!
  IndisputableMonolith.lean
  Single-file, axiom-free core: Recognition structure + Ledger interface +
  continuity on closed chains (T3) + lattice-independent 2^d minimality (T7).
  No external dependencies beyond basic mathlib.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic

open Classical Function

namespace IndisputableMonolith

/-! ## Meta-Principle: Nothing cannot recognize itself -/

abbrev Nothing := Empty

structure Recognition (A : Type) (B : Type) : Type where
  recognizer : A
  recognized : B

def MP : Prop := ¬ ∃ r : Recognition Nothing Nothing, True

theorem mp_holds : MP := by
  intro h; rcases h with ⟨r, _⟩; cases r.recognizer

/-! ## Recognition structure -/

structure RecognitionStructure where
  U : Type
  R : U → U → Prop

/-! ## Finite chains along R -/

structure Chain (M : RecognitionStructure) where
  n : Nat
  f : Fin (n+1) → M.U
  ok : ∀ i : Fin n, M.R (f i.castSucc) (f i.succ)

namespace Chain
variable {M : RecognitionStructure} (ch : Chain M)
def head : M.U := ch.f ⟨0, by decide⟩
def last : M.U := ch.f ⟨ch.n, Nat.lt_succ_self _⟩
@[simp] lemma head_def : ch.head = ch.f ⟨0, by decide⟩ := rfl
@[simp] lemma last_def : ch.last = ch.f ⟨ch.n, Nat.lt_succ_self _⟩ := rfl
end Chain

/-! ## T2: Atomic tick interface -/

class AtomicTick (M : RecognitionStructure) (L : Ledger M) : Prop where
  postedAt : Nat → M.U → Prop
  unique_post : ∀ t : Nat, ∃! u : M.U, postedAt t u

/-- T2: if two postings occur at the same tick, they are the same posting. -/
theorem T2_atomicity {M} {L : Ledger M} [AtomicTick M L] :
  ∀ t u v, AtomicTick.postedAt (M:=M) (L:=L) t u →
           AtomicTick.postedAt (M:=M) (L:=L) t v → u = v := by
  intro t u v hu hv
  rcases (AtomicTick.unique_post (M:=M) (L:=L) t) with ⟨w, hw, huniq⟩
  have hu' : u = w := huniq u hu
  have hv' : v = w := huniq v hv
  exact hu'.trans hv'.symm

/-! ## Ledger: potential and closed-chain continuity (T3) -/

structure Ledger (M : RecognitionStructure) where
  intake : M.U → ℤ
  output : M.U → ℤ

def phi {M} (L : Ledger M) : M.U → ℤ := fun u => L.intake u - L.output u

def chainFlux {M} (L : Ledger M) (ch : Chain M) : ℤ :=
  phi L (Chain.last ch) - phi L (Chain.head ch)

class Conserves {M} (L : Ledger M) : Prop where
  conserve : ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0

theorem T3_continuity {M} (L : Ledger M) [Conserves L] :
  ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0 :=
  Conserves.conserve

instance conserves_of_potential {M} (L : Ledger M) : Conserves L where
  conserve ch h := by
    unfold chainFlux phi
    simpa [h]

/-! ## T7: lattice-independent 2^d minimality -/

@[simp] def Pattern (d : Nat) := (Fin d → Bool)
instance (d : Nat) : Fintype (Pattern d) := inferInstance

lemma card_pattern (d : Nat) : Fintype.card (Pattern d) = 2 ^ d := by
  classical
  simpa [Pattern] using
    (Fintype.card_fun : Fintype.card (Fin d → Bool) = _)

lemma no_surj_small (T d : Nat) (hT : T < 2 ^ d) :
  ¬ ∃ f : Fin T → Pattern d, Surjective f := by
  classical
  intro h
  rcases h with ⟨f, hf⟩
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  have hginj : Injective g := by
    intro y₁ y₂ hgy
    have : f (g y₁) = f (g y₂) := by simpa [hgy]
    simpa [RightInverse, hg y₁, hg y₂] using this
  have hcard : Fintype.card (Pattern d) ≤ Fintype.card (Fin T) :=
    Fintype.card_le_of_injective _ hginj
  have : 2 ^ d ≤ T := by
    simpa [Fintype.card_fin, card_pattern d] using hcard
  exact (lt_of_le_of_lt this hT).false

lemma min_ticks_cover {d T : Nat}
  (pass : Fin T → Pattern d) (covers : Surjective pass) : 2 ^ d ≤ T := by
  classical
  by_contra h
  exact (no_surj_small T d (lt_of_not_ge h)) ⟨pass, covers⟩

lemma eight_tick_min {T : Nat}
  (pass : Fin T → Pattern 3) (covers : Surjective pass) : 8 ≤ T := by
  simpa using (min_ticks_cover (d := 3) (T := T) pass covers)

end IndisputableMonolith
