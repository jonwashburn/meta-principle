import IndisputableMonolith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Basic

open Classical
open scoped BigOperators

namespace IndisputableMonolith
namespace Optional

variable {α : Type} {d : Nat}

variable [DecidableEq α] [IndisputableMonolith.BoundedStep α d]

local notation "stepR" => (IndisputableMonolith.BoundedStep.step : α → α → Prop)
local notation "nbrs" => (IndisputableMonolith.BoundedStep.neighbors : α → Finset α)

/-- Generic union bound for `Finset.bind`: card of the union is ≤ sum of cards. -/
lemma card_bind_le_sum' {σ β : Type} [DecidableEq σ] [DecidableEq β]
  (s : Finset σ) (t : σ → Finset β) : (s.bind t).card ≤ ∑ a ∈ s, (t a).card := by
  classical
  -- Map each part into disjoint labeled blocks in σ × β and project back
  let emb (a : σ) : β ↪ σ × β := ⟨fun b => (a, b), by intro b₁ b₂ h; simpa using congrArg Prod.snd h⟩
  let parts : σ → Finset (σ × β) := fun a => (t a).map (emb a)
  have hdisj : ∀ {a₁} (ha₁ : a₁ ∈ s) {a₂} (ha₂ : a₂ ∈ s), a₁ ≠ a₂ → Disjoint (parts a₁) (parts a₂) := by
    intro a₁ ha₁ a₂ ha₂ hne
    refine Finset.disjoint_left.mpr ?h
    intro p hp1 hp2
    rcases Finset.mem_map.mp hp1 with ⟨b₁, hb₁, rfl⟩
    rcases Finset.mem_map.mp hp2 with ⟨b₂, hb₂, hpair⟩
    have : a₁ = a₂ := by simpa using congrArg Prod.fst hpair
    exact (hne this).elim
  -- cardinality of disjoint bind equals sum of cardinals
  have hcardParts : (s.bind parts).card = ∑ a ∈ s, (parts a).card := by
    simpa using Finset.card_bind (s:=s) (t:=parts) hdisj
  -- Projection σ×β → β sends each block back into t a
  let proj : σ × β → β := Prod.snd
  have himg : (s.bind parts).image proj ⊆ (s.bind t) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    rcases Finset.mem_bind.mp hp with ⟨a, ha, hp'⟩
    rcases Finset.mem_map.mp hp' with ⟨b, hb, hbmap⟩
    have : proj (a, b) = b := rfl
    have hb' : b ∈ t a := by simpa [parts, emb] using hb
    exact Finset.mem_bind.mpr ⟨a, ha, by simpa [this] using hb'⟩
  -- conclude card(union) ≤ sum of cards via projection
  calc
    (s.bind t).card ≤ ((s.bind parts).image proj).card :=
      Finset.card_le_of_subset (by intro z hz; exact himg hz)
    _ ≤ (s.bind parts).card := Finset.card_image_le
    _ = ∑ a ∈ s, (parts a).card := hcardParts
    _ = ∑ a ∈ s, (t a).card := by
          refine Finset.sum_congr rfl (by intro a ha; simp [parts])

/-- Kinematics induced by the bounded step relation. -/
def K : Causality.Kinematics α := { step := fun x y => stepR x y }

/-- Exact-n cover, obtained by repeatedly expanding by neighbors. -/
def coverExact : Nat → α → Finset α
| 0, x => {x}
| n+1, x => (coverExact n x).bind (fun y => nbrs y)

/-- Any vertex reachable in exactly `n` steps is contained in `coverExact n`. -/
lemma mem_coverExact_of_reachN {x y : α} :
  ∀ {n}, Causality.ReachN (K : Causality.Kinematics α) n x y → y ∈ coverExact n x := by
  intro n h; induction h with
  | zero => simp [coverExact]
  | @succ n x y z hxy hyz ih =>
      have hy : y ∈ coverExact n x := ih
      have hz : z ∈ nbrs y := (IndisputableMonolith.BoundedStep.step_iff_mem y z).1 hyz
      exact Finset.mem_bind.mpr ⟨y, hy, hz⟩

/-- The cardinality of `coverExact n x` is bounded by `d^n`. -/
lemma card_coverExact_le_pow (x : α) :
  ∀ n, (coverExact n x).card ≤ d ^ n := by
  classical
  -- Main induction
  intro n; induction n with
  | zero => simp [coverExact]
  | succ n ih =>
      have : (coverExact (n+1) x).card
            ≤ ∑ y ∈ coverExact n x, (nbrs y).card := by
        simpa [coverExact] using card_bind_le_sum' (coverExact n x) nbrs
      -- bound each neighbor set by d
      have : (coverExact (n+1) x).card
            ≤ ∑ _y ∈ coverExact n x, d :=
        le_trans this <| Finset.sum_le_sum (by
          intro y hy; exact IndisputableMonolith.BoundedStep.degree_bound_holds y)
      -- sum of constants over a finset is `card * d`
      have : (coverExact (n+1) x).card ≤ (coverExact n x).card * d := by
        simpa using (le_trans this (by
          simpa using Finset.card_nsmul d (coverExact n x)))
      exact le_trans this (by simpa [Nat.pow_succ] using Nat.mul_le_mul_right d ih)

/-- `ballCover n x` collects all shells up to radius n. -/
def ballCover (n : Nat) (x : α) : Finset α :=
  (Finset.range (n+1)).bind (fun k => coverExact k x)

/-- Membership in the n-ball implies membership in `ballCover`. -/
lemma mem_ballCover_of_inBall {x y : α} {n : Nat}
  (hin : Causality.inBall (K : Causality.Kinematics α) x n y) :
  y ∈ ballCover n x := by
  rcases hin with ⟨k, hk, hreach⟩
  have hk' : k ∈ Finset.range (n+1) := Nat.memRange.mpr (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hk (Nat.lt_succ_self _)))
  have hy : y ∈ coverExact k x := mem_coverExact_of_reachN (x:=x) (y:=y) hreach
  exact Finset.mem_bind.mpr ⟨k, hk', hy⟩

/-- Cardinality bound for `ballCover`: `card ≤ ∑_{k=0}^n d^k`. -/
lemma card_ballCover_le_geom_sum (x : α) (n : Nat) :
  (ballCover n x).card ≤ ∑ k in Finset.range (n+1), d ^ k := by
  classical
  -- Use the generic union bound on `bind`
  have h : (ballCover n x).card
            ≤ ∑ k ∈ Finset.range (n+1), (coverExact k x).card := by
    simpa [ballCover] using card_bind_le_sum' (Finset.range (n+1)) (fun k => coverExact k x)
  -- bound each shell by d^k
  refine le_trans h ?_;
  refine Finset.sum_le_sum (by
    intro k hk; exact card_coverExact_le_pow (x:=x) k)

/-- n-ball cardinality bound under degree ≤ d: any finite over-approximation `ballCover` obeys the geometric bound,
    and it contains the graph-theoretic n-ball from `Causality`. -/
theorem inBall_card_le_geom_sum {x y : α} {n : Nat}
  (hin : Causality.inBall (K : Causality.Kinematics α) x n y) :
  (ballCover n x).card ≤ ∑ k in Finset.range (n+1), d ^ k ∧ y ∈ ballCover n x := by
  refine ⟨card_ballCover_le_geom_sum (x:=x) n, mem_ballCover_of_inBall (x:=x) (y:=y) hin⟩

end Optional
end IndisputableMonolith
