# Lean Roadmap: Constants and Classical Bridge

Purpose: Complete a sorry-free Lean development that derives RS structures through to constants (existing classical and RS-specific), then proves explicit correspondences to classical physics. Keep proofs modular, auditable, and compatible with Mathlib.

## Goals
- Derive and expose constants with clear dependencies:
  - RS-specific: φ (fixed point), τ0 (fundamental tick), ℓ0 (voxel length), E_coh, λ_rec
  - Classical: c, ħ, G, α (with presentation-time numeric mapping)
- Formalize bridges (Twin/Bridge/Novel) per theorem: T1–T8 → classical correspondences.
- Preserve sorry-free status and avoid extra axioms.

## Current baseline (already in `IndisputableMonolith.lean`)
- T1–T8: mp_holds, T2 atomicity, T3 continuity, T4 potential uniqueness (reach/inBall/component; up to constant), T6 existence/minimality (2^D, 8 in 3D)
- Cost uniqueness (T5) on ℝ>0 via `Jcost` interfaces; log-model scaffold and demos
- ClassicalBridge: gauge classes for T4; T2 schedule; BFS `ballFS` with `mem_ballFS_iff_ballP`

## High-level module plan (keep monolith, add focused namespaces)
- Namespace Constants: symbolic constants and defining relations
- Namespace Bridge: per-theorem classical equivalences
- Namespace Causality+: cone cardinal bounds (finite degree)
- Namespace Action: Euler–Lagrange equivalence for J in local quadratic regime
- Namespace Spectra: mass ladder structures and invariants (structural, no numerics)
- Namespace Quantum: path-weight interface and symmetrization result statements
- Namespace Gravity: ILG kernel formalization and continuity→effective source bridge

## Detailed tasks and target theorems

### 1) Causality bounds (complete cone results)
- Define cardinality recursion for `ballFS`:
  - `ballFS_card_succ ≤ ballFS_card + d * ballFS_card`
  - Conclude `(ballFS x n).card ≤ (1 + d)^n`
- Theorems:
  - `cone_card_geometric (d) : (ballFS x n).card ≤ (1 + d)^n`
  - Bridge: discrete → continuum cone; define `c := ℓ0 / τ0`
- Dependencies: `BoundedStep.degree_bound_holds`; `Finset.card_bind` lemmas from Mathlib

### 2) Constants (symbolic definitions + relations)
- Symbols (structure/defs):
  - `def φ : ℝ := (1 + Real.sqrt 5) / 2`
  - `constant τ0 : ℝ` (tick) and `ℓ0 : ℝ` (voxel length), assume positive
  - `def c := ℓ0 / τ0`
  - `constant E_coh : ℝ` with axiom-free definitional tag `E_coh = φ^(-5)` (store as def if using normalized units; otherwise keep relation lemma)
  - `def ħ := E_coh * τ0 / (2 * Real.pi)`
  - `def λ_rec := Real.sqrt (ħ * G / (c^3))` (with `constant G : ℝ` symbol; classical numeric mapping in Methods)
  - `constant α : ℝ` with relation lemma (bridge-only; numeric mapping at presentation)
- Theorems:
  - `c_def : c = ℓ0 / τ0`
  - `hbar_def : ħ = E_coh * τ0 / (2π)`
  - `lambda_rec_def : λ_rec = sqrt (ħ * G / c^3)`
  - Positivity: `0 < τ0`, `0 < ℓ0` ⇒ `0 < c`; `0 < E_coh` ⇒ `0 < ħ` ⇒ `0 < λ_rec`
- Notes: implement as defs + lemmas; keep CODATA numbers out of Lean core (provide mapping hooks only)

### 3) T5 → Stationary action (bridge)
- Local quadratic regime: show that minimizing `Jcost` on multiplicative positives corresponds to minimizing Dirichlet energy on log-axis (EL conditions match).
- Theorems:
  - `EL_equiv_local : (AveragingDerivation F) ⇒ EulerLagrange(F∘exp) matches Dirichlet form`
  - Promote `Jcost` instance to main-text bridge lemma
- Dependencies: existing `Jcost`, `JensenSketch`, convexity facts from Mathlib

### 4) T7 sampling bound (bridge)
- Discrete Nyquist/Shannon analogue:
  - From `min_ticks_cover` generalize to injectivity of encoding below 2^D; produce lemma naming sampling obstruction
- Theorems:
  - `nyquist_obstruction : T < 2^D ⇒ no_surjection_to_patterns`

### 5) T8 δ units (bridge)
- Already have subgroup equivalence for δ ≠ 0; add contextual unit mapping structure:
  - `structure UnitMapping := (toZ : Δ-subgroup ≃ ℤ) (context : Type) ...`
- Theorems:
  - `delta_quantization_context : δ ≠ 0 ⇒ exists mapping matching classical quantization (up to scale)`

### 6) Spectra (mass ladder, structural only)
- Define ladder:
  - `def Mass (B : ℝ) (r : ℤ) (f : ℝ) := B * E_coh * φ^(r + f)` with constraints: `B ∈ {2^k}`
- Theorems:
  - Closure under rung shifts; monotonicity; minimality constructor (sketch → full proof)
- Bridge hooks:
  - `structure PDGMap := (label : String) (r : ℤ) (f : ℝ) (Bpow : ℤ)` without numerics

### 7) Quantum (interfaces)
- Path weight interface:
  - `class PathWeight (γ) := (C : γ → ℝ) (P := fun γ => Real.exp (-(C γ)))`
- Theorems (interface-level):
  - `born_rule_iface : normalization + linearity ⇒ P ∝ |ψ|^2`
  - `bose_fermi_iface : permutation invariance ⇒ (sym/antisym)`
- Keep these as propositions/structures to be instantiated later

### 8) Gravity (ILG)
- Formalize symbols: `w(k,a)` kernel and galaxy solver interface
- Bridge: continuity (T3) ⇒ effective source, linear growth limit lemma
- Theorems (interface-level):
  - `ilg_effective_source : continuity + kernel assumptions ⇒ modified Poisson form`

## ClassicalBridge expansions to implement
- T2: add coarse-graining lemma (sums→integrals) statement skeleton
- T3: alias present (`DiscreteContinuity`)
- T4: DONE (gauge classes, unique constant, gauge class equality)
- T5: add `EL_equiv_local` lemma
- T6: map τ0 definition; keep in Methods-only
- T7: add `nyquist_obstruction`
- T8: add `delta_quantization_context`

## File organization
- Keep `IndisputableMonolith.lean` as canonical; add new namespaces inside it first.
- Optionally later split into:
  - `RS/Constants.lean`, `RS/Bridge.lean`, `RS/Causality.lean`, `RS/Action.lean`, `RS/Spectra.lean`, `RS/Quantum.lean`, `RS/Gravity.lean`
- Maintain `lakefile.lean` minimal; no extra deps beyond Mathlib.

## Acceptance criteria
- All new theorems are sorry-free and `#print axioms` shows none beyond core Lean/Mathlib
- `lake build` succeeds locally
- For constants: provide definitional lemmas and positivity; keep numerics in external mapping
- For bridges: each theorem has a corresponding `ClassicalBridge.*` lemma usable in paper Methods

## Execution plan (milestones)
- M1: Cone cardinal bound theorems (Causality) + c := ℓ0/τ0 mapping lemmas
- M2: Constants namespace (`c`, `ħ`, `λ_rec`, `E_coh`) + positivity
- M3: T5 EL bridge lemma
- M4: T7 sampling bridge; T8 context mapping
- M5: Spectra structural lemmas
- M6: Quantum/Gravity interface-level lemmas
- M7: Refactor into modules (optional), update docs and bridge source

## Developer checklist
- After each step: `lake build` and `#print axioms` spot-checks
- Update `RS_Classical_Bridge_Source.txt` proof status flags when lemmas land
- Commit granular edits; keep PRs focused per milestone
