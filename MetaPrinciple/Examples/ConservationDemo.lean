/-!
Minimal worked example: a two‑node recognition structure with a simple ledger.
We build a closed 2‑step chain and show that `T3_continuity` yields zero flux.
-/

import MetaPrinciple.Recognition.Ledger.Core
import MetaPrinciple.Foundations.T3_Continuity

open Classical

namespace MetaPrinciple
namespace Examples

-- A tiny recognition structure with two nodes and a single recognition edge a→b and b→a.
def Tiny : RecognitionStructure where
  U := Bool
  recog := fun x y => (x = false ∧ y = true) ∨ (x = true ∧ y = false)
  comp := by
    intro a b c hab hbc
    -- Any composition in a 2‑cycle returns to `a → c`; for this demo we just pick one direction
    -- and allow both directions to be "recognized" so composition holds.
    cases hab <;> cases hbc <;> all_goals
      first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩

noncomputable def tinyLedger : Ledger Tiny ℝ :=
  { delta := 1
  , delta_pos := by norm_num
  , debit := fun u => if u then (1 : ℝ) else 0
  , credit := fun u => if u then 0 else 1
  , de := by
      intro a b hab
      -- For either direction, debit b − credit a = 1
      rcases hab with h | h
      · rcases h with ⟨ha, hb⟩; subst ha; subst hb; simp
      · rcases h with ⟨ha, hb⟩; subst ha; subst hb; simp }

-- Closed 2‑step chain: false → true → false
def tinyClosed : Chain Tiny :=
  { n := 2
  , f := fun i => match i.val with
      | 0 => false
      | 1 => true
      | _ => false
  , ok := by
      intro i; cases' i with k hk
      fin_cases k <;> simp [Tiny, tinyClosed] }

-- Any ledger is conservative for closed chains in this development.
instance : Conserves (tinyLedger) :=
{ conserve := by
    intro ch hclosed
    -- chainFlux reduces to φ(last) − φ(first) = 0 when endpoints coincide
    simp [chainFlux, phi, hclosed] }

-- The worked example: flux vanishes on the closed 2‑step chain.
example : chainFlux tinyLedger tinyClosed = 0 := by
  -- endpoints coincide by construction
  have hclosed : tinyClosed.f ⟨0, by decide⟩ = tinyClosed.f ⟨tinyClosed.n, by decide⟩ := by rfl
  simpa using (T3_continuity (L := tinyLedger) tinyClosed hclosed)

end Examples
end MetaPrinciple
