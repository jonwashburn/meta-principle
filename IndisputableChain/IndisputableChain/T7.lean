import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open Classical Function

namespace IndisputableChain

/-- A `d`‑bit parity pattern is a function `Fin d → Bool`. -/
@[simp] def Pattern (d : Nat) := (Fin d → Bool)
instance instFintypePattern (d : Nat) : Fintype (Pattern d) := by
  classical
  dsimp [Pattern]
  infer_instance

/-- Cardinality: `|Pattern d| = 2^d`. -/
lemma card_pattern (d : Nat) : Fintype.card (Pattern d) = 2 ^ d := by
  classical
  -- `card (ι → α) = card α ^ card ι`
  simpa [Pattern, Fintype.card_fin] using
    (Fintype.card_fun : Fintype.card (Fin d → Bool) = (Fintype.card Bool) ^ (Fintype.card (Fin d)))

/-- There is no surjection from a set of size `T` onto `2^d` patterns when `T < 2^d`. -/
lemma no_surj_small (T d : Nat) (hT : T < 2 ^ d) : ¬ ∃ f : Fin T → Pattern d, Surjective f := by
  classical
  intro h
  rcases h with ⟨f, hf⟩
  -- A surjection admits a right inverse `g`
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  have hginj : Injective g := by
    intro y₁ y₂ hgy
    have : f (g y₁) = f (g y₂) := congrArg f hgy
    simpa [hg y₁, hg y₂] using this
  -- Hence `card (Pattern d) ≤ card (Fin T) = T`
  have hcard : Fintype.card (Pattern d) ≤ Fintype.card (Fin T) :=
    Fintype.card_le_of_injective _ hginj
  have : 2 ^ d ≤ T := by simpa [Fintype.card_fin, card_pattern d] using hcard
  exact (lt_of_le_of_lt this hT).false

/-- Any pass (finite sequence) that covers all parity patterns has length ≥ `2^d`. -/
lemma min_ticks_cover {d T : Nat} (pass : Fin T → Pattern d) (covers : Surjective pass) : 2 ^ d ≤ T := by
  classical
  by_contra h
  exact (no_surj_small T d (lt_of_not_ge h)) ⟨pass, covers⟩

/-- Lifting the bound through a parity map from arbitrary state space. -/
lemma min_ticks_cover_states {d T : Nat} {State : Type}
    (parity : State → Pattern d) (seq : Fin T → State)
    (covers : Surjective (fun i => parity (seq i))) : 2 ^ d ≤ T := by
  classical
  have : Surjective (fun i : Fin T => (parity (seq i))) := covers
  simpa using (min_ticks_cover (d := d) (T := T) (fun i => parity (seq i)) this)

/-- Specialization `d = 3`: eight‑tick minimality. -/
lemma eight_tick_min {T : Nat} (pass : Fin T → Pattern 3) (covers : Surjective pass) : 8 ≤ T := by
  simpa using (min_ticks_cover (d := 3) (T := T) pass covers)

end IndisputableChain
