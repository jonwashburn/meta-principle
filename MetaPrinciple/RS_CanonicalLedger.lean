/ -
RS_CanonicalLedger.lean
Author: Recognition Physics Institute (c) 2025

Contents
1) Canonical ledger L₀ on a vertex set U:
   - carrier PG(U) := FreeAbelianGroup U
   - balance : U → PG(U)   (the universal potential)
   - post a b := balance b - balance a
   - post_comp / post_symm
   - Universal property via FreeAbelianGroup.lift

2) Discrete Stokes on the 3-cube (Bool × Bool × Bool):
   - For any additive target group G and any potential ψ : V → G,
     the oriented sum around any square face is 0 (telescopes).

3) T7 lower bounds (eight-beat / hypercube):
   - If f : Fin T → Bool×Bool×Bool is surjective, then 8 ≤ T.
   - Generalization: if f : Fin T → (Fin D → Bool) is surjective, then 2^D ≤ T.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Equiv.Basic

set_option autoImplicit true

universe u v

namespace RS

/-- The canonical potential group on `U`: the free abelian group on `U`. -/
abbrev PG (U : Type u) := FreeAbelianGroup U

/-- The universal "balance" (potential) element corresponding to a vertex `u : U`. -/
def balance {U : Type u} (u : U) : PG U := FreeAbelianGroup.of u

/-- The canonical posting along the oriented edge `a → b`. -/
def post {U : Type u} (a b : U) : PG U := balance b - balance a

@[simp] lemma post_symm {U : Type u} (a b : U) :
    post b a = - post a b := by
  -- (b - a) = -(a - b)
  simp [post, balance, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

@[simp] lemma post_comp {U : Type u} (a b c : U) :
    post a c = post a b + post b c := by
  -- (c - a) = (b - a) + (c - b)
  simp [post, balance, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

section Universal
variable {U : Type u} {G : Type v} [AddCommGroup G]

/-- The universal hom from `PG U` induced by a chosen potential `ψ : U → G`. -/
def liftBalance (ψ : U → G) : PG U →+ G := FreeAbelianGroup.lift ψ

@[simp] lemma liftBalance_balance (ψ : U → G) (u : U) :
    liftBalance (U:=U) ψ (balance u) = ψ u := by
  simp [liftBalance, balance]

@[simp] lemma liftBalance_post (ψ : U → G) (a b : U) :
    liftBalance ψ (post a b) = ψ b - ψ a := by
  simp [post, sub_eq_add_neg, liftBalance]

/-- **Universal property**: a hom `h` is uniquely determined by its values on `balance`. -/
lemma liftBalance_unique (ψ : U → G) (h : PG U →+ G)
    (hbal : ∀ u, h (balance u) = ψ u) :
    h = liftBalance ψ := by
  ext u; simpa [balance, liftBalance] using hbal u

end Universal

/-
Discrete Stokes on the 3-cube
We work with vertices V := Bool × Bool × Bool, and take values in any AddCommGroup G.
-/

section Stokes
variable {G : Type v} [AddCommGroup G]

/-- Simple 4-cycle telescoping identity in any additive commutative group. -/
lemma telescope4 (a b c d : G) :
    (b - a) + (c - b) + (d - c) + (a - d) = 0 := by
  -- rearrange and cancel
  -- we can use `abel` for additive commutative groups
  abel

/-- Vertex type for the 3-cube. -/
abbrev V := (Bool × Bool × Bool)

/-- A face in the XY-plane at fixed `z` satisfies Stokes (oriented loop sum = 0). -/
theorem stokes_face_XY (ψ : V → G) (z : Bool) :
    (ψ (true,  false, z) - ψ (false, false, z)) +
    (ψ (true,  true,  z) - ψ (true,  false, z)) +
    (ψ (false, true,  z) - ψ (true,  true,  z)) +
    (ψ (false, false, z) - ψ (false, true,  z)) = 0 := by
  simpa using
    telescope4 (a := ψ (false, false, z))
               (b := ψ (true,  false, z))
               (c := ψ (true,  true,  z))
               (d := ψ (false, true,  z))

/-- A face in the YZ-plane at fixed `x` satisfies Stokes. -/
theorem stokes_face_YZ (ψ : V → G) (x : Bool) :
    (ψ (x, false, true) - ψ (x, false, false)) +
    (ψ (x, true,  true) - ψ (x, false, true )) +
    (ψ (x, true,  false) - ψ (x, true,  true )) +
    (ψ (x, false, false) - ψ (x, true,  false)) = 0 := by
  simpa using
    telescope4 (a := ψ (x, false, false))
               (b := ψ (x, false, true))
               (c := ψ (x, true,  true))
               (d := ψ (x, true,  false))

/-- A face in the XZ-plane at fixed `y` satisfies Stokes. -/
theorem stokes_face_XZ (ψ : V → G) (y : Bool) :
    (ψ (true,  y, false) - ψ (false, y, false)) +
    (ψ (true,  y, true ) - ψ (true,  y, false)) +
    (ψ (false, y, true ) - ψ (true,  y, true )) +
    (ψ (false, y, false) - ψ (false, y, true )) = 0 := by
  simpa using
    telescope4 (a := ψ (false, y, false))
               (b := ψ (true,  y, false))
               (c := ψ (true,  y, true ))
               (d := ψ (false, y, true ))

/-
Interpretation: if you take `ψ := balance` (the PG potential), then
`ψ v₂ - ψ v₁ = post v₁ v₂`. Each of the three lemmas states that the
oriented sum of `post` around any square face is zero, i.e. the discrete
curl of a gradient vanishes (Stokes).
-/

end Stokes

/-
T7: Eight-beat / hypercube lower bounds.
We prove cardinality lower bounds from surjectivity. No graph theory needed.
-/
namespace T7

/-- Card of Bool is 2. -/
lemma card_bool : Fintype.card Bool = 2 := by decide

/-- Vertices of the 3-cube and their cardinality. -/
abbrev V3 := (Bool × Bool × Bool)

lemma card_V3 : Fintype.card V3 = 8 := by
  classical
  -- Reassociate to use card_prod twice
  have h₁ :
      Fintype.card V3
        = Fintype.card ((Bool × Bool) × Bool) := by
    -- `Equiv.prodAssoc` gives a bijection between (α×β)×γ and α×(β×γ)
    -- We'll use it in reverse direction to reshape the triple product.
    simpa [V3] using
      Fintype.card_congr (Equiv.prodAssoc Bool Bool Bool).symm
  calc
    Fintype.card V3
        = Fintype.card ((Bool × Bool) × Bool) := h₁
    _   = Fintype.card (Bool × Bool) * Fintype.card Bool := by
            simpa [Fintype.card_prod]
    _   = (Fintype.card Bool * Fintype.card Bool) * Fintype.card Bool := by
            simpa [Fintype.card_prod]
    _   = (2 * 2) * 2 := by simp [card_bool]
    _   = 8 := by norm_num

/-- If `f : Fin T → V3` hits every vertex (surjective), then `8 ≤ T`. -/
theorem lowerBound_cube {T : ℕ} (f : Fin T → V3) (hs : Function.Surjective f) :
    8 ≤ T := by
  classical
  -- From a surjection `f`, choose a right-inverse `g` with `f (g v) = v`.
  rcases hs.hasRightInverse with ⟨g, hg⟩
  -- That right-inverse is injective.
  have hg_inj : Function.Injective g := by
    intro v₁ v₂ h
    have := congrArg f h
    simpa [hg v₁, hg v₂] using this
  -- Injectivity gives a cardinality inequality.
  have hcard :
      Fintype.card V3 ≤ Fintype.card (Fin T) :=
    Fintype.card_le_of_injective _ hg_inj
  -- Convert to `8 ≤ T`.
  simpa [card_V3, Fintype.card_fin] using hcard

/-- General hypercube with `D` bits: vertices are functions `Fin D → Bool`. -/
abbrev VD (D : ℕ) := (Fin D → Bool)

/-- Cardinality of the `D`-dimensional hypercube: `2^D`. -/
lemma card_VD (D : ℕ) : Fintype.card (VD D) = 2 ^ D := by
  classical
  -- `Fintype.card_fun` : card (α → β) = (card β)^(card α)
  simpa [VD, card_bool] using (Fintype.card_fun (Fin D) Bool)

/-- General T7 bound: a surjective `f : Fin T → (Fin D → Bool)` forces `2^D ≤ T`. -/
theorem lowerBound_hypercube {D T : ℕ}
    (f : Fin T → VD D) (hs : Function.Surjective f) :
    2 ^ D ≤ T := by
  classical
  rcases hs.hasRightInverse with ⟨g, hg⟩
  have hg_inj : Function.Injective g := by
    intro v₁ v₂ h
    have := congrArg f h
    simpa [hg v₁, hg v₂] using this
  have hcard :
      Fintype.card (VD D) ≤ Fintype.card (Fin T) :=
    Fintype.card_le_of_injective _ hg_inj
  simpa [card_VD, Fintype.card_fin] using hcard

end T7

/-
Notes for integration:

• Use `balance : U → PG U` as your canonical ledger potential (rename of your old φ_ledger).
  Any concrete potential ψ : U → G gives a unique hom `liftBalance ψ : PG U →+ G`.

• The discrete Stokes lemmas become exactly the “boundary sum = 0” facts for
  `ψ := balance` or for any additive target ledger you obtain by pushing `balance`
  forward along a homomorphism.

• The T7 lemmas give you the cardinal lower bounds you were stating informally,
  now as small, clean theorems you can reuse.
-/

end RS
