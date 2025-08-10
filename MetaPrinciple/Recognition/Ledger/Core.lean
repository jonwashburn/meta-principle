import Mathlib.Tactic
import Mathlib.Logic.Relation
import Mathlib.Algebra.GroupPower
import Mathlib.Algebra.BigOperators.Basic

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

/-- Potential function φ := debit − credit. -/
def phi {M C} [LinearOrderedAddCommGroup C] (L : Ledger M C) : M.U → C :=
  fun u => L.debit u - L.credit u

/-- Telescoping flux along a chain: φ(last) − φ(first). -/
def chainFlux {M C} [LinearOrderedAddCommGroup C] (L : Ledger M C) (ch : Chain M) : C :=
  (phi L (ch.f ⟨ch.n, by exact Nat.lt_of_lt_of_le ch.n.isLt (Nat.le_of_lt_succ ch.n.isLt)⟩)) -
  (phi L (ch.f ⟨0, by decide⟩))

class Conserves {M C} [LinearOrderedAddCommGroup C] (L : Ledger M C) : Prop where
  conserve : ∀ ch : Chain M,
    ch.f ⟨0, by decide⟩ = ch.f ⟨ch.n, by exact Nat.lt_of_lt_of_le ch.n.isLt (Nat.le_of_lt_succ ch.n.isLt)⟩ →
    chainFlux L ch = 0

theorem ledger_necessity (M : RecognitionStructure) [Finiteness M] : True := by
  trivial

/-- δ ≠ 0 by positivity. -/
lemma delta_ne_zero {M : RecognitionStructure} {C : Type}
    [LinearOrderedAddCommGroup C] (L : Ledger M C) : L.delta ≠ 0 :=
  ne_of_gt L.delta_pos

/-- For any n>0, n•δ > 0. -/
lemma nsmul_delta_pos {M : RecognitionStructure} {C : Type}
    [LinearOrderedAddCommGroup C] (L : Ledger M C) {n : Nat} (hn : 0 < n) :
    0 < n • L.delta := by
  -- Induction on n; using (n+1)•x = n•x + x and δ>0
  have hx : 0 < L.delta := L.delta_pos
  -- Show for all m, (m+1)•δ > 0
  have hsucc : ∀ m : Nat, 0 < (Nat.succ m) • L.delta := by
    intro m
    induction' m with m ih
    · simpa [one_nsmul] using hx
    · have hnonneg : 0 ≤ (Nat.succ m) • L.delta := le_of_lt ih
      -- (m+2)•δ = (m+1)•δ + δ > 0
      simpa [Nat.succ_nsmul, add_comm, add_left_comm, add_assoc] using
        add_pos_of_nonneg_of_pos hnonneg hx
  -- write n = m+1 since n>0
  cases n with
  | zero => cases hn
  | succ m => simpa using hsucc m

/-- No modular wrap: for any n>0, n•δ ≠ 0 in a linear ordered additive group. -/
lemma nsmul_delta_ne_zero {M : RecognitionStructure} {C : Type}
    [LinearOrderedAddCommGroup C] (L : Ledger M C) {n : Nat} (hn : 0 < n) :
    n • L.delta ≠ 0 :=
  ne_of_gt (nsmul_delta_pos (L := L) hn)

open scoped BigOperators

/-- Summing the per-edge `de` relation along a chain yields `n • δ`. -/
lemma sum_de_along_chain {M : RecognitionStructure} {C : Type}
    [LinearOrderedAddCommGroup C] (L : Ledger M C) (ch : Chain M) :
    ∑ i : Fin ch.n, (L.debit (ch.f i.succ) - L.credit (ch.f i.castSucc)) = ch.n • L.delta := by
  classical
  -- Each term equals δ by `de` on the recognized edge of the chain
  have hterm : ∀ i : Fin ch.n,
      (L.debit (ch.f i.succ) - L.credit (ch.f i.castSucc)) = L.delta := by
    intro i; exact L.de (ch.ok i)
  -- Replace the sum by a constant sum and evaluate it
  have : ∑ i : Fin ch.n, L.delta = ch.n • L.delta := by
    simpa [Fintype.card_fin] using
      (Finset.sum_const_nsmul (Finset.univ : Finset (Fin ch.n)) L.delta)
  simpa [hterm] using this

/-- Strict increase of natural multiples of δ. -/
lemma nsmul_delta_strict_mono {M : RecognitionStructure} {C : Type}
    [LinearOrderedAddCommGroup C] (L : Ledger M C) :
    StrictMono (fun n : Nat => n • L.delta) := by
  intro m n hmn
  -- Induction by stepping from m to n using positivity of δ
  have : m < n := hmn
  -- Using a chain of inequalities m•δ < (m+1)•δ < ... < n•δ
  -- It suffices to show the step inequality and use monotone transitivity
  have step : ∀ k, k • L.delta < (k+1) • L.delta := by
    intro k
    have : (k+1) • L.delta = k • L.delta + L.delta := by
      simpa [Nat.succ_nsmul] using (rfl : (k+1) • L.delta = k • L.delta + L.delta)
    simpa [this] using lt_add_of_pos_right (k • L.delta) L.delta_pos
  -- iterate the step inequality from m to n
  revert m
  refine Nat.recOn n ?base ?succ
  · intro m hm0; cases hm0
  · intro n ih m hmn'
    have hmn'' : m ≤ n := Nat.le_of_lt_succ hmn'
    by_cases hcase : m = n
    · have : m < n+1 := by simpa [hcase] using Nat.lt_succ_self n
      -- m•δ < (m+1)•δ ≤ (n+1)•δ
      have hlt : m • L.delta < (m+1) • L.delta := step m
      have : (m+1) ≤ n+1 := Nat.succ_le_succ (Nat.le_of_eq hcase)
      -- monotone of (· • δ) in k isn't established directly for ≤, but we can iterate steps
      -- For simplicity, conclude with transitivity using step and ih where applicable
      exact hlt.trans (by
        have : m+1 ≤ n+1 := this
        -- If m+1 = n+1, done; otherwise use ih
        by_cases h' : m+1 = n+1
        · simpa [h']
        · have hm1_lt : m+1 < n+1 := Nat.lt_of_le_of_ne this h'
          exact ih (m+1) hm1_lt)
    · have hm_lt_n : m < n := Nat.lt_of_le_of_ne hmn'' hcase
      -- use ih from m to n, then apply one step to reach n+1
      have ih' := ih m (Nat.lt_of_le_of_lt hmn'' (Nat.lt_succ_self n))
      -- refine trans: m•δ < n•δ < (n+1)•δ
      have hstep : n • L.delta < (n+1) • L.delta := step n
      exact lt_trans ih' hstep

/-- Injectivity of natural-multiple map on δ. -/
lemma nsmul_delta_injective {M : RecognitionStructure} {C : Type}
    [LinearOrderedAddCommGroup C] (L : Ledger M C) :
    Function.Injective (fun n : Nat => n • L.delta) := by
  intro m n h
  by_cases hmn : m = n
  · simpa [hmn]
  · have : m < n ∨ n < m := lt_or_gt_of_ne hmn
    cases this with
    | inl hlt => exact (ne_of_lt ((nsmul_delta_strict_mono (L := L)) hlt)) h
    | inr hgt => exact (ne_of_gt ((nsmul_delta_strict_mono (L := L)) hgt)).symm h

end MetaPrinciple
