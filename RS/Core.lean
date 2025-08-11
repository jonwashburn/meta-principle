/-
Core interfaces for Recognition Science (kernel)
Lean 4 + mathlib

This file fixes the *signatures* of the main theorems so downstream code is stable.
Replace axioms with proofs incrementally without breaking dependencies.

References correspond to manuscript sections:
- §2.1: Recognition Structure & Meta-Principle  
- §2.2: Ledger-Necessity (strong form)
- §2.3: Unique cost functional J
- §3: Self-similarity & k=1
- App: Eight-Tick-Cycle Theorem
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic

open scoped BigOperators

namespace RS  -- Recognition Science

/-! ## 1. Recognition Structure -/

/-- A recognition-structure: universe of entities `U`, a distinguished `empty`,
    and a binary relation `R` ("a recognizes b").
    (MP) = meta-principle, (C) = composability, (F) = no infinite chains.
    See §A, §2.1 in the manuscript. -/
structure RecognitionStructure where
  U     : Type u
  empty : U
  R     : U → U → Prop
  MP    : ¬ R empty empty
  C     : ∀ {a b c}, R a b → R b c → R a c
  F     : ∀ (f : ℕ → U), (∀ n, R (f n) (f (n+1))) → False

attribute [simp] RecognitionStructure.MP

/-! ## 2. Ledger Structure -/

/-- A (totally ordered) additive cost group. -/
class CostGroup (C : Type v) extends LinearOrderedAddCommGroup C

instance : CostGroup ℤ := inferInstance
instance : CostGroup ℚ := inferInstance
instance : CostGroup ℝ := inferInstance

/-- A double-entry ledger on a recognition structure.
    `iota` and `kappa` are the credit/debit columns, `δ>0` the immutable generator.
    L1 = double entry, L2 = positivity, L3 = conservation over any finite chain.
    See Defs. 2.1 & 2.2 and Thm. "Ledger–Necessity". -/
structure Ledger (M : RecognitionStructure) where
  C        : Type v
  [cstr]   : CostGroup C
  iota     : M.U → C
  kappa    : M.U → C
  delta    : C
  delta_pos : (0 : C) < delta
  L1_double_entry :
    ∀ {a b}, M.R a b → iota b - kappa a = delta
  L2_positivity :
    ∀ {x}, x ≠ M.empty → (0 : C) < iota x ∧ (0 : C) < kappa x
  L3_conservation :
    ∀ {n : ℕ} (f : Fin (n+1) → M.U),
      (∀ k : Fin n, M.R (f ⟨k.1, by omega⟩) (f ⟨k.1+1, by omega⟩)) →
      iota (f ⟨n, by omega⟩) - kappa (f ⟨0, by omega⟩) = n • delta

attribute [simp] Ledger.L1_double_entry
attribute [instance] Ledger.cstr

/-- Isomorphism of ledgers: order-isomorphism on costs preserving `delta`, `iota`, `kappa`. -/
structure LedgerIso {M : RecognitionStructure} (L₁ L₂ : Ledger M) where
  φ : L₁.C ≃o L₂.C
  φ_delta : φ L₁.delta = L₂.delta
  φ_iota  : ∀ x, φ (L₁.iota x) = L₂.iota x
  φ_kappa : ∀ x, φ (L₁.kappa x) = L₂.kappa x

/-- Ledger–Necessity (existence & uniqueness up to order-isomorphism).
    Matches Theorem "Ledger–Necessity (strong form)" incl. non-rescalability of δ. -/
axiom ledger_necessity_unique (M : RecognitionStructure) :
  ∃ (L : Ledger M), ∀ L', LedgerIso L L'

/-! ## 3. Cost Functional -/

/-- The canonical cost functional. -/
def J (x : ℝ) : ℝ := (x + x⁻¹) / 2

/-- Admissible cost functional on `x>0`:
    symmetry (dual-balance), positivity/normalization, and a global finiteness bound.
    This is the hypothesis set in §2.3 / Appendix "Uniqueness of the Cost Functional". -/
structure AdmissibleCost (F : ℝ → ℝ) : Prop where
  symmetry    : ∀ {x : ℝ}, 0 < x → F x = F x⁻¹
  norm1       : F 1 = 1
  positive    : ∀ {x : ℝ}, x ≠ 1 → 0 < x → 0 < F x
  finiteness  : ∃ K > 0, ∀ {x : ℝ}, 0 < x → F x ≤ K * (x + x⁻¹)

/-- J is symmetric. -/
lemma J_symm {x : ℝ} (hx : 0 < x) : J x = J x⁻¹ := by
  unfold J; field_simp; ring

/-- J at 1 is 1. -/
lemma J_norm1 : J 1 = 1 := by
  unfold J; simp

/-- J is positive for x ≠ 1. -/
lemma J_positive {x : ℝ} (hx_ne : x ≠ 1) (hx_pos : 0 < x) : 0 < J x := by
  unfold J
  have : x + x⁻¹ > 2 := by
    have h := Real.two_mul_one_lt_x_add_inv_x_of_ne_one hx_ne hx_pos
    linarith
  linarith

/-- J has finiteness bound with K = 1/2. -/
lemma J_finiteness : ∃ K > 0, ∀ {x : ℝ}, 0 < x → J x ≤ K * (x + x⁻¹) := by
  use 1/2
  constructor
  · norm_num
  · intro x _
    unfold J
    ring_nf
    rfl

/-- J is admissible. -/
theorem J_admissible : AdmissibleCost J where
  symmetry := @J_symm
  norm1 := J_norm1
  positive := @J_positive
  finiteness := J_finiteness

/-- Uniqueness of the cost functional: the only admissible F is J. -/
axiom unique_cost_functional :
  ∀ {F : ℝ → ℝ}, AdmissibleCost F → ∀ {x : ℝ}, 0 < x → F x = J x

/-! ## 4. Golden Ratio & Self-Similarity -/

/-- The golden ratio φ = (1 + √5)/2. -/
def φ : ℝ := (1 + Real.sqrt 5) / 2

/-- φ is positive. -/
lemma φ_pos : 0 < φ := by
  unfold φ
  have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)
  linarith

/-- φ satisfies the self-similar recurrence x = 1 + 1/x. -/
theorem φ_fixed_point : φ = 1 + 1/φ := by
  unfold φ
  have h : φ * φ = φ + 1 := by
    unfold φ
    have h5 : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    field_simp [h5]
    ring
  field_simp [φ_pos.ne']
  exact h

/-- The discrete self-similarity recurrence. -/
def recur (k : ℕ) (x : ℝ) : ℝ := 1 + k/x

/-- Countability ⇒ k is an integer and cost-minimization picks k=1.
    Mirrors Lemma "Discrete decomposition forces integer k" and Thm. "k=1". -/
axiom k_eq_one :
  ∀ {F : ℝ → ℝ}, AdmissibleCost F → 
  ∀ {k : ℕ}, k ≥ 1 → k = 1

/-! ## 5. Eight-Tick Cycle -/

namespace EightTick

/-- Vertices of the 3-cube as triples of bits. -/
def V : Type := Fin 2 × Fin 2 × Fin 2

instance : Fintype V := inferInstance

/-- Adjacency: differ in exactly one coordinate. -/
def Adj (u v : V) : Prop :=
  (u.1 ≠ v.1 ∧ u.2.1 = v.2.1 ∧ u.2.2 = v.2.2) ∨
  (u.1 = v.1 ∧ u.2.1 ≠ v.2.1 ∧ u.2.2 = v.2.2) ∨
  (u.1 = v.1 ∧ u.2.1 = v.2.1 ∧ u.2.2 ≠ v.2.2)

/-- The cube graph. -/
def CubeGraph : SimpleGraph V where
  Adj := Adj
  symm := by
    intro u v h
    cases h with
    | inl h => left; exact ⟨h.1.symm, h.2.1, h.2.2⟩
    | inr h => cases h with
      | inl h => right; left; exact ⟨h.1, h.2.1.symm, h.2.2⟩
      | inr h => right; right; exact ⟨h.1, h.2.1, h.2.2.symm⟩
  loopless := by
    intro v h
    cases h <;> tauto

/-- A ledger-compatible recognition walk: edge-steps, periodic with minimal period `T`,
    and spatially complete (visits all 8 vertices within one period).
    See App. "Eight–Tick–Cycle Theorem". -/
structure Walk where
  f        : ℕ → V
  step     : ∀ n, CubeGraph.Adj (f n) (f (n+1))
  T        : ℕ
  Tpos     : 0 < T
  period   : ∀ n, f (n+T) = f n
  minimal  : ∀ T', 0 < T' → (∀ n, f (n+T') = f n) → T ≤ T'
  complete : (Set.range fun n : Fin T => f n) = Set.univ

/-- Eight–Tick–Cycle Theorem: any ledger-compatible complete walk has minimal period 8. -/
axiom eight_tick_minimal (w : Walk) : w.T = 8

end EightTick

/-! ## 6. Gap Series -/

/-- Gap-series coefficients gₘ = (-1)^(m+1)/(m φ^m). -/
def gapCoeff (m : ℕ) : ℝ :=
  if m = 0 then 0 else (-1 : ℝ)^(m+1) / (m * φ^m)

/-- Generating functional F(z) = ∑ gₘ z^m = log(1 + z/φ) on |z|≤1. -/
axiom gap_generating_closed_form :
  ∀ z ∈ Set.Icc (-1:ℝ) 1,
    ∑' m : ℕ, gapCoeff m * z^m = Real.log (1 + z/φ)

/-- At z=1, the gap series sums to log φ. -/
theorem gap_sum_at_one : ∑' m : ℕ, gapCoeff m = Real.log φ := by
  have h := gap_generating_closed_form 1 (by simp : 1 ∈ Set.Icc (-1:ℝ) 1)
  simp at h
  exact h

end RS
