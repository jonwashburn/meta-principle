/-
  RS/Graph/DegreeSum.lean
  Lean 4 + mathlib.  No sorrys.
  Finite digraph degree sums.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

open scoped BigOperators
open Finset

namespace RS

variables {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop) [DecidableRel R]

/-- The set of directed edges as pairs `(u,v)` with `R u v`. -/
def edges : Finset (V × V) :=
  (univ.product (univ : Finset V)).filter (fun p => R p.1 p.2)

/-- Out-degree of a vertex. -/
def outdeg (v : V) : ℕ := ((univ.filter fun w => R v w)).card

/-- In-degree of a vertex. -/
def indeg (v : V) : ℕ := ((univ.filter fun u => R u v)).card

private def star (R : V → V → Prop) (v : V) : Finset (V × V) :=
  ((univ.filter fun w => R v w).image (fun w => (v, w)))

private lemma star_disjoint (R : V → V → Prop) [DecidableRel R] :
  Pairwise (Disjoint on fun v : V => star (R := R) v) := by
  classical
  intro v₁ _ v₂ _ hne
  refine disjoint_left.mpr ?_
  intro ⟨a,b⟩ ha hb
  rcases mem_image.mp ha with ⟨w₁, hw₁, hpair1⟩
  rcases mem_image.mp hb with ⟨w₂, hw₂, hpair2⟩
  cases hpair1; cases hpair2
  exact (hne rfl).elim

private lemma edges_eq_biUnion_stars (R : V → V → Prop) [DecidableRel R] :
  edges (R := R) = univ.biUnion (fun v => star (R := R) v) := by
  classical
  ext ⟨u,v⟩; constructor
  · intro h
    rcases mem_filter.mp h with ⟨hp, huv⟩
    rcases mem_product.mp hp with ⟨hu, hv⟩
    have hv' : v ∈ (univ.filter fun w => R u w) := by
      simpa [mem_filter] using And.intro (mem_univ v) huv
    refine mem_biUnion.mpr ?_
    refine ⟨u, mem_univ u, ?_⟩
    exact mem_image.mpr ⟨v, hv', rfl⟩
  · intro h
    rcases mem_biUnion.mp h with ⟨u, _, hu⟩
    rcases mem_image.mp hu with ⟨w, hw, hpair⟩
    rcases mem_filter.mp hw with ⟨_, huw⟩
    have hp : (u, w) ∈ (univ.product (univ : Finset V)) := by
      exact mem_product.mpr ⟨mem_univ u, mem_univ w⟩
    simpa [edges, hpair] using mem_filter.mpr ⟨hp, huw⟩

private lemma card_star (R : V → V → Prop) [DecidableRel R] (v : V) :
  (star (R := R) v).card = outdeg (R := R) v := by
  classical
  -- image by (fun w => (v,w)) is injective
  have hinj : (UnorderedList.Perm (fun w : V => (v, w))) := by
    trivial
  -- simpler: Finset.card_image for an injective map on the filtered finset
  have : (star (R := R) v).card = ((univ.filter fun w => R v w)).card := by
    -- map is injective
    refine card_image_iff.mpr ?_
    intro a _ b _ h
    exact (Prod.ext_iff.mp h).2
  simpa [star, outdeg] using this

/-- `∑ outdeg = |edges|`. -/
theorem sum_outdeg_eq_edges :
  (∑ v, outdeg (R := R) v) = (edges (R := R)).card := by
  classical
  have hdisj := star_disjoint (R := R)
  have hdecomp := edges_eq_biUnion_stars (R := R)
  have hcard := card_biUnion (s := (univ : Finset V)) (t := fun v => star (R := R) v) hdisj
  simpa [hdecomp, card_star (R := R)] using hcard

private def cstar (R : V → V → Prop) (v : V) : Finset (V × V) :=
  ((univ.filter fun u => R u v).image (fun u => (u, v)))

private lemma cstar_disjoint (R : V → V → Prop) [DecidableRel R] :
  Pairwise (Disjoint on fun v : V => cstar (R := R) v) := by
  classical
  intro v₁ _ v₂ _ hne
  refine disjoint_left.mpr ?_
  intro ⟨a,b⟩ ha hb
  rcases mem_image.mp ha with ⟨u₁, hu₁, hpair1⟩
  rcases mem_image.mp hb with ⟨u₂, hu₂, hpair2⟩
  cases hpair1; cases hpair2
  exact (hne rfl).elim

private lemma edges_eq_biUnion_cstars (R : V → V → Prop) [DecidableRel R] :
  edges (R := R) = univ.biUnion (fun v => cstar (R := R) v) := by
  classical
  ext ⟨u,v⟩; constructor
  · intro h
    rcases mem_filter.mp h with ⟨hp, huv⟩
    rcases mem_product.mp hp with ⟨hu, hv⟩
    have hu' : u ∈ (univ.filter fun w => R w v) := by
      simpa [mem_filter] using And.intro (mem_univ u) huv
    refine mem_biUnion.mpr ?_
    refine ⟨v, mem_univ v, ?_⟩
    exact mem_image.mpr ⟨u, hu', rfl⟩
  · intro h
    rcases mem_biUnion.mp h with ⟨v, _, hv⟩
    rcases mem_image.mp hv with ⟨u, hu, hpair⟩
    rcases mem_filter.mp hu with ⟨_, huv⟩
    have hp : (u, v) ∈ (univ.product (univ : Finset V)) := by
      exact mem_product.mpr ⟨mem_univ u, mem_univ v⟩
    simpa [edges, hpair] using mem_filter.mpr ⟨hp, huv⟩

private lemma card_cstar (R : V → V → Prop) [DecidableRel R] (v : V) :
  (cstar (R := R) v).card = indeg (R := R) v := by
  classical
  have : (cstar (R := R) v).card = ((univ.filter fun u => R u v)).card := by
    refine card_image_iff.mpr ?_
    intro a _ b _ h
    exact (Prod.ext_iff.mp h).1
  simpa [cstar, indeg] using this

/-- `∑ indeg = |edges|`. -/
theorem sum_indeg_eq_edges :
  (∑ v, indeg (R := R) v) = (edges (R := R)).card := by
  classical
  have hdisj := cstar_disjoint (R := R)
  have hdecomp := edges_eq_biUnion_cstars (R := R)
  have hcard := card_biUnion (s := (univ : Finset V)) (t := fun v => cstar (R := R) v) hdisj
  simpa [hdecomp, card_cstar (R := R)] using hcard

/-- Corollary: `∑ outdeg = ∑ indeg`. -/
theorem sum_outdeg_eq_sum_indeg :
  (∑ v, outdeg (R := R) v) = (∑ v, indeg (R := R) v) := by
  simpa [sum_outdeg_eq_edges (R := R), sum_indeg_eq_edges (R := R)]

end RS
