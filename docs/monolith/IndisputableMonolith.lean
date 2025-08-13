/-!
  IndisputableMonolith.lean
  Single-file, axiom-free core: Recognition structure + Ledger interface +
  continuity on closed chains (T3) + lattice-independent 2^d minimality (T7).
  No external dependencies beyond basic mathlib.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

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

/-! ## J, φ, and k=1 strict minimization -/

def J (x : ℝ) : ℝ := (x + x⁻¹) / 2 - 1

lemma two_le_add_inv_add (x : ℝ) (hx : 0 < x) : 2 ≤ x + x⁻¹ := by
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx
  have hsq : 0 ≤ (x - 1) ^ 2 := by exact sq_nonneg (x - 1)
  have : 0 ≤ ((x - 1) ^ 2) / x := by exact div_nonneg hsq (le_of_lt hx)
  have hiden : ((x - 1) ^ 2) / x = x + x⁻¹ - 2 := by
    field_simp [hxne]; ring
  have : 0 ≤ x + x⁻¹ - 2 := by simpa [hiden]
  linarith

lemma two_lt_add_inv_add_of_ne_one (x : ℝ) (hx : 0 < x) (hne : x ≠ 1) : 2 < x + x⁻¹ := by
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx
  have hsq : 0 < (x - 1) ^ 2 := by
    have : x - 1 ≠ 0 := sub_ne_zero.mpr (by simpa [ne_comm] using hne)
    exact pow_two_pos_of_ne_zero (x - 1) this
  have : 0 < ((x - 1) ^ 2) / x := by exact div_pos hsq hx
  have hiden : ((x - 1) ^ 2) / x = x + x⁻¹ - 2 := by
    field_simp [hxne]; ring
  have : 0 < x + x⁻¹ - 2 := by simpa [hiden]
  linarith

lemma J_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ J x := by
  unfold J
  have : 2 ≤ x + x⁻¹ := two_le_add_inv_add x hx
  linarith

lemma J_pos_of_ne_one {x : ℝ} (hx : 0 < x) (hne : x ≠ 1) : 0 < J x := by
  unfold J
  have : 2 < x + x⁻¹ := two_lt_add_inv_add_of_ne_one x hx hne
  linarith

lemma diff_sum_inv (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
  (y + y⁻¹) - (x + x⁻¹) = (y - x) * (1 - (x*y)⁻¹) := by
  field_simp [hx, hy]
  ring

/-- J is strictly increasing on [1, ∞). -/
lemma J_strictMono_on_ge_one {x y : ℝ} (hx1 : 1 ≤ x) (hxy : x < y) : J x < J y := by
  have hx0 : 0 < x := lt_of_le_of_lt (by norm_num) hx1
  have hy0 : 0 < y := lt_trans (by norm_num) hxy
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hyne : y ≠ 0 := ne_of_gt hy0
  have hprod : x*y > 1 := by
    have hx1' : 1 ≤ x := hx1
    have hy1' : 1 < y := lt_of_le_of_lt hx1 hxy
    have : (1:ℝ) < x*y := by
      have hxpos : 0 < x := hx0
      have := mul_lt_mul_of_pos_right hy1' hxpos
      simpa using this
    exact this
  have hfactor : 0 < 1 - (x*y)⁻¹ := sub_pos.mpr (by
    have : (x*y)⁻¹ < 1 := by
      have hxymulpos : 0 < x*y := mul_pos_of_pos_of_pos hx0 hy0
      exact inv_lt_one_iff.mpr (by exact_mod_cast (lt_trans (by norm_num) hprod))
    simpa using this)
  have hyx : 0 < y - x := sub_pos.mpr hxy
  have hdiff : 0 < (y + y⁻¹) - (x + x⁻¹) := by
    have : (y + y⁻¹) - (x + x⁻¹) = (y - x) * (1 - (x*y)⁻¹) :=
      diff_sum_inv x y hxne hyne
    have := mul_pos_of_pos_of_pos hyx hfactor
    simpa [this]
  have : 0 < J y - J x := by
    unfold J
    have := div_pos hdiff (by norm_num : (0:ℝ) < 2)
    linarith
  linarith

def φ : ℝ := (1 + Real.sqrt 5) / 2

def recurrence (k : ℕ) (x : ℝ) : Prop := x = 1 + (k : ℝ) / x

lemma phi_fixed : recurrence 1 φ := by
  unfold recurrence φ
  field_simp
  have : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  ring_nf; rw [this]; ring

def xk (k : ℕ) : ℝ := (1 + Real.sqrt (1 + 4 * (k : ℝ))) / 2

lemma xk_solves (k : ℕ) : recurrence k (xk k) := by
  unfold recurrence xk
  field_simp
  have : Real.sqrt (1 + 4 * (k:ℝ)) ^ 2 = 1 + 4 * (k:ℝ) := by
    have hpos : (0:ℝ) ≤ 1 + 4 * (k:ℝ) := by
      have : (0:ℝ) ≤ 4 * (k:ℝ) := by exact mul_nonneg (by norm_num) (by exact_mod_cast Nat.cast_nonneg k)
      linarith
    simpa using Real.sq_sqrt hpos
  ring_nf; rw [this]; ring

lemma phi_eq_xk1 : φ = xk 1 := by
  unfold φ xk; simp

lemma xk_gt_phi_of_ge_two {k : ℕ} (hk : 2 ≤ k) : xk k > φ := by
  unfold xk φ
  have : Real.sqrt (1 + 4 * (k:ℝ)) > Real.sqrt 5 := by
    have hlt : (1 + 4 * (k:ℝ)) > 5 := by
      have : (k:ℝ) ≥ 2 := by exact_mod_cast hk
      linarith
    exact Real.sqrt_lt_sqrt_iff.mpr hlt
  nlinarith

lemma phi_ge_one : 1 ≤ φ := by
  unfold φ; have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5); nlinarith

theorem k_equals_one (k : ℕ) (hk : 2 ≤ k) : J (xk k) > J φ := by
  have hgt : xk k > φ := xk_gt_phi_of_ge_two hk
  exact J_strictMono_on_ge_one phi_ge_one hgt

end IndisputableMonolith
