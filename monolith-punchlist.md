## Monolith.lean Fortification Punchlist

Goal: Make `MetaPrinciple/Monolith.lean` a single-file, copy/pasteable artifact that is logically tight (no placeholders), self-consistent, and easy to upload to browser LLMs.

### Build/structure hygiene (single-file quality)
- [ ] Add header metadata in `Monolith.lean` (generation time, git hash, number of modules).
- [ ] Ensure imports are fully de‑duplicated; keep only necessary `import Mathlib.*` and `import` from local modules (or none if truly self-contained).
- [ ] Keep per-file section markers but strip editor-only comments; preserve all math content.
- [ ] Provide a small `make-monolith` script/README note for re-generation to prevent drift.

### T1 Ledger (existence and uniqueness)
- [x] Existence witness `ledgerFromFree`: use `delta=1`, `debit=1`, `credit=0` so `debit b − credit a = δ` holds.
- [ ] Prove cone pointedness in `QuotientLedger` (replace TODO) using `fromQuotient` and conservation to show `q∈P ∧ −q∈P ⇒ q=0`.
- [ ] Upgrade `Preorder` → `PartialOrder` by a real `le_antisymm` (depends on cone pointedness).
- [ ] Provide order‑isomorphism uniqueness (complete the `toOrderIso` sketch).
- [ ] Exclusions: prove no k‑ary/modular wrap for δ>0 (use `nsmul_delta_ne_zero`).
- [ ] δ non‑rescalability: strengthen and expose as a theorem (injectivity and rigidity under normalization).

### T2 Atomicity
- [ ] Construct `[TickSchedule]` or derive from well‑founded `step` on `RecognitionStructure`. Tie `postedAt` to recognition walk.
- [ ] Document countability: per chain/event count is finite under `Finiteness`.

### T3 Conservation (discrete continuity)
- [ ] Replace the vacuous `Conserves` instance with a derivation from the ledger equation: define edge flux from `de`, prove closed-chain sum telescopes to zero.
- [ ] Implement discrete Stokes/boundary flux equals chain flux for voxel faces; connect to `Chain`.

### T4 Cost functional (uniqueness)
- [ ] Keep the Laurent route as the canonical proof: provide concrete `LogConvexAnalytic` hypotheses or directly furnish `LaurentData` for the cost.
- [ ] Remove placeholder fields; add minimal real statements (log‑convex on ln‑axis, analyticity on `ℂ \ {0}`) and prove `LaurentData`.
- [ ] Expose a top-level `theorem` instantiating T4 for the canonical `J` used elsewhere.

### T5 Self-similarity (k = 1; φ)
- [ ] Add convergence results for the k=1 orbit toward φ (domain of attraction, monotone bounds).
- [ ] Connect Σ(k) minimality with T4 canonical `J` (explicit reference/lemma chain).

### T6 Minimal spatial dimension d=3
- [ ] Refine `StableLinking` assumptions: encode minimal invariants (Jordan in d=2, Alexander in d≥4, Hopf in d=3) as typed facts.
- [ ] Keep Hopf link cost bound via canonical `J`; add multi-scale/aggregation lemmas.

### T7 Minimal period T = 2^D (Gray codes)
- [ ] Provide an explicit `[HasGrayCode D]` instance (inductive Gray‑code generator) to remove the existence typeclass assumption.
- [ ] Present `period = 2^D` as a single theorem combining existence and minimality.

### T8 Causality (max speed c = Lmin/τ0)
- [ ] Choose an explicit metric on `VD D := Fin D → Bool` (Hamming) and prove `dist(x,y) ≤ n` for `n` one-bit steps.
- [ ] Combine with atomic tick duration `τ0` and minimal hop length `Lmin` to prove the light‑cone bound `dist ≤ n·Lmin` and `speed ≤ c`.

### Monolith-only ergonomics for LLM upload
- [ ] Add a compact index at the top (search map: symbol → section line range).
- [ ] Provide a minimal “entry point” section with the eight-foundation theorems in one place (already available via `AllInOne.lean`; replicate summary in `Monolith.lean`).
- [ ] Optionally include tiny `example` blocks that reference each theorem to validate symbol resolution in isolation.

### External/tooling
- [ ] Pin Lean/mathlib/aesop/batteries/proofwidgets versions in a separate doc; the monolith should build against a known toolchain.
- [ ] Remove macOS resource files from `.lake/**` in repo (non‑UTF‑8) or ignore them.

### Quick wins (recommended order)
1. T1: cone pointedness → `PartialOrder` → order‑iso uniqueness.
2. T7: implement `[HasGrayCode D]` to fully discharge general existence.
3. T3: replace conservation with a real telescoping proof using `de`.
4. T4: finalize Laurent assumptions → canonical uniqueness for `J`.
5. T8: finalize light‑cone bound on `VD D` with Hamming metric.


