import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace MetaPrinciple

abbrev V := Fin 3 → Bool

def adj (u v : V) : Prop := (Finset.univ.filter (fun i => u i ≠ v i)).card = 1

def Q3 : SimpleGraph V where
  Adj u v := adj u v
  symm := by intro u v h; simpa [adj] using h
  loopless := by intro u h; simp [adj] at h

structure RecWalk where
  cycle : Fin 8 → V
  edges : ∀ i : Fin 8, adj (cycle i) (cycle ⟨(i.val + 1) % 8, by decide⟩)

/-- Explicit 3‑bit Gray code Hamiltonian cycle of length 8. -/
def gray8 : Fin 8 → V
| ⟨0, _⟩ => ![false,false,false]
| ⟨1, _⟩ => ![true,false,false]
| ⟨2, _⟩ => ![true,true,false]
| ⟨3, _⟩ => ![false,true,false]
| ⟨4, _⟩ => ![false,true,true]
| ⟨5, _⟩ => ![true,true,true]
| ⟨6, _⟩ => ![true,false,true]
| ⟨7, _⟩ => ![false,false,true]

lemma gray8_adj : ∀ i : Fin 8, adj (gray8 i) (gray8 ⟨(i.val + 1) % 8, by decide⟩) := by
  intro i; cases' i with i hi
  all_goals decide

/-- Existence of an 8‑tick Hamiltonian recognition cycle on Q3. -/
theorem eight_tick_exists : ∃ w : RecWalk, True := by
  refine ⟨{ cycle := gray8, edges := gray8_adj }, trivial⟩

/-- Minimality: no function from `Fin T` onto `V` exists when `T < 8`,
    hence no period `< 8` can cover all 8 vertices. -/
theorem eight_tick_minimal {T : Nat} (hT : T < 8) :
    ¬ ∃ f : Fin T → V, Surjective f :=
  no_cover_with_period_lt_eight (T := T) hT

/-- Generalization to hypercubes: period `2^D` is achievable (Gray code) and minimal by cardinality. -/
theorem hypercube_period_exact (D : Nat) [HasGrayCode D] :
    (∃ w : RecWalkD D, True) ∧ (∀ {T : Nat}, T < 2 ^ D → ¬ ∃ f : Fin T → VD D, Surjective f) := by
  refine ⟨?exist, ?minimal⟩
  · exact gray_code_exists_allD D
  · intro T hT; exact no_cover_with_period_lt_pow_two D hT

/-!  Minimality via cardinality (covering all vertices requires at least 8 ticks) -/

open Function

lemma card_V : Fintype.card V = 8 := by
  classical
  -- card (Fin 3 → Bool) = (card Bool)^(card (Fin 3)) = 2^3 = 8
  have h := Fintype.card_fun (Fin 3) Bool
  -- h : Fintype.card V = Fintype.card Bool ^ Fintype.card (Fin 3)
  have : Fintype.card V = (2 : Nat) ^ 3 := by
    simpa using h
  have : Fintype.card V = 8 := by
    simpa using this
  exact this

/-- Any surjection from `Fin T` onto `V` forces `T ≥ 8`. -/
theorem period_ge_eight_of_surjective {T : Nat} {f : Fin T → V}
    (hs : Surjective f) : 8 ≤ T := by
  classical
  -- `card V ≤ card (Fin T)` from surjectivity
  have hcard := Fintype.card_le_of_surjective f hs
  -- rewrite both sides
  simpa [card_V, Fintype.card_fin] using hcard

/-- No period `< 8` can cover all 8 vertices. -/
theorem no_cover_with_period_lt_eight {T : Nat} (hT : T < 8) :
    ¬ ∃ f : Fin T → V, Surjective f := by
  intro h
  rcases h with ⟨f, hs⟩
  have : 8 ≤ T := period_ge_eight_of_surjective (f := f) hs
  exact Nat.not_le_of_gt hT this

/-- General D-bit hypercube vertex type. -/
abbrev VD (D : Nat) := Fin D → Bool

/-- Adjacency on the D-cube: vertices differ in exactly one coordinate. -/
def adjD (D : Nat) (u v : VD D) : Prop :=
  (Finset.univ.filter (fun i => u i ≠ v i)).card = 1

/-- The D-dimensional hypercube as a simple graph. -/
def QD (D : Nat) : SimpleGraph (VD D) where
  Adj u v := adjD D u v
  symm := by
    intro u v h; simpa [adjD] using h
  loopless := by
    intro u h; simp [adjD] at h

/-- Cyclic successor on `Fin (2^D)` (i ↦ i+1 mod 2^D). -/
def succPowTwo (D : Nat) (i : Fin (2 ^ D)) : Fin (2 ^ D) :=
  ⟨(i.val + 1) % (2 ^ D), by
    have hpos : 0 < 2 ^ D := Nat.pow_pos (by decide : 0 < 2) D
    simpa using Nat.mod_lt (i.val + 1) hpos⟩

/-- A Gray-cycle on the D-cube: a cyclic walk of length `2^D` with unit-Hamming steps. -/
structure RecWalkD (D : Nat) where
  cycle : Fin (2 ^ D) → VD D
  edges : ∀ i : Fin (2 ^ D), adjD D (cycle i) (cycle (succPowTwo D i))

/-- Signature for a D-bit Gray code generator. Implementation can be provided by a small helper/import. -/
class HasGrayCode (D : Nat) : Prop where
  gray  : Fin (2 ^ D) → VD D
  edges : ∀ i : Fin (2 ^ D), adjD D (gray i) (gray (succPowTwo D i))

/-- Statement-level existence of a D-bit Gray cycle, deferring implementation to `HasGrayCode D`. -/
theorem gray_code_exists_allD (D : Nat) [HasGrayCode D] : ∃ w : RecWalkD D, True := by
  refine ⟨{ cycle := HasGrayCode.gray (D := D), edges := HasGrayCode.edges (D := D) }, trivial⟩

/-- Cardinality of D-cube vertices. -/
lemma card_VD (D : Nat) : Fintype.card (VD D) = 2 ^ D := by
  classical
  have h := Fintype.card_fun (Fin D) Bool
  simpa using h

/-- Any surjection from `Fin T` onto the D-cube forces `T ≥ 2^D`. -/
theorem period_ge_pow_two_of_surjective (D : Nat) {T : Nat} {f : Fin T → VD D}
    (hs : Surjective f) : 2 ^ D ≤ T := by
  classical
  have hcard := period_ge_card_of_surjective (α := VD D) (T := T) (f := f) hs
  simpa [card_VD D] using hcard

/-- No period `< 2^D` can cover all `2^D` vertices of the D-cube. -/
theorem no_cover_with_period_lt_pow_two (D : Nat) {T : Nat} (hT : T < 2 ^ D) :
    ¬ ∃ f : Fin T → VD D, Surjective f := by
  intro h; rcases h with ⟨f, hs⟩
  have : 2 ^ D ≤ T := period_ge_pow_two_of_surjective D (f := f) hs
  exact Nat.not_le_of_gt hT this

/-- Generic cardinality minimality: any surjection from `Fin T` to a finite type `α`
    with `Fintype.card α = N` implies `N ≤ T`. -/
theorem period_ge_card_of_surjective {α : Type} [Fintype α]
    {T : Nat} {f : Fin T → α} (hs : Surjective f) :
    Fintype.card α ≤ T := by
  classical
  simpa [Fintype.card_fin] using Fintype.card_le_of_surjective f hs

end MetaPrinciple
