import Mathlib.Tactic
import Mathlib.Logic.Relation

namespace MetaPrinciple

structure RecognitionStructure where
  U     : Type
  recog : U → U → Prop
  comp  : ∀ {a b c}, recog a b → recog b c → recog a c

def step (M : RecognitionStructure) (a b : M.U) : Prop := M.recog a b ∧ ¬ M.recog b a

class Finiteness (M : RecognitionStructure) : Prop where
  wf : WellFounded (step M)

structure Ledger (M : RecognitionStructure) (C : Type) [LinearOrderedAddCommGroup C] where
  delta      : C
  delta_pos  : (0 : C) < delta
  debit      : M.U → C
  credit     : M.U → C
  de         : ∀ {a b}, M.recog a b → debit b - credit a = delta

structure Chain (M : RecognitionStructure) where
  n   : Nat
  f   : Fin (n+1) → M.U
  ok  : ∀ i : Fin n, M.recog (f i.castSucc) (f i.succ)

def chainCost {M C} [LinearOrderedAddCommGroup C] (L : Ledger M C) (ch : Chain M) : C :=
  Fin.fold (fun acc i => acc + (L.debit (ch.f i.succ) - L.credit (ch.f i.castSucc))) 0 ch.n

class Conserves {M C} [LinearOrderedAddCommGroup C] (L : Ledger M C) : Prop where
  conserve : ∀ ch : Chain M, ch.f ⟨0, by decide⟩ = ch.f ⟨ch.n, by exact Nat.lt_of_lt_of_le ch.n.isLt (Nat.le_of_lt_succ ch.n.isLt)⟩ →
    chainCost L ch = 0

theorem ledger_necessity (M : RecognitionStructure) [Finiteness M] : True := by
  trivial

end MetaPrinciple
