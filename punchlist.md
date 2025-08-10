## Punchlist: Meta‑Principle → T1–T8 and Repo

### Meta (Nothing cannot recognize itself)
- [ ] Add brief docs reference and cross‑link to manuscript proof; keep proof minimal.

### T1 Ledger necessity & uniqueness
- [ ] Replace placeholders in `Recognition/Ledger/QuotientLedger.lean` with real proofs:
  - [ ] Positive cone pointedness (`cone_pointed`) without placeholders.
  - [ ] Antisymmetry and `PartialOrder` via cone; remove trivial endings.
  - [ ] Uniqueness up to order‑isomorphism (`uniqueness_up_to_orderIso`).
- [ ] Prove existence assumptions:
  - [ ] Derive or justify `[Finiteness M]` from earlier structure, or clearly mark as an axiom.
- [ ] Exclusions and normalization:
  - [ ] Exclude k‑ary/modular encodings formally; show double‑entry with δ>0 forbids modular wrap.
  - [ ] δ non‑rescalability theorem (fixes scale once normalization chosen).
- [ ] Connect `ledgerFromFree` to quotient ledger as canonical witness; show the universal map is order‑preserving and conservative.

### T2 Atomicity & countability
- [ ] Construct `[AtomicTick M C L]` from prior structure:
  - [ ] From well‑founded `step` relation or from T7 Gray cycle in D=3.
- [ ] Tie `postedAt` to recognition walk; prove countability of events per chain.

### T3 Dual‑balance ⇒ discrete continuity
- [ ] Derive `[Conserves L]` from double‑entry axioms (not just for `ledgerFromFree`).
- [ ] Implement discrete divergence/Stokes on chains; show `chainFlux = 0` for closed chains without using placeholders.

### T4 Unique cost functional J(x) = ½(x + 1/x)
- [ ] Remove heuristic step in `Cost/Functional.cost_unique`; provide a rigorous proof chain.
- [ ] Flesh out `LogConvexAnalytic` with real statements (log‑convexity on ln‑axis, analyticity on ℂ∖{0}).
- [ ] Prove `LaurentData` ⇒ only first harmonic survives; use normalization to get c₁ = 1/2.
- [ ] Derive cost symmetry `CF.symm` from ledger invariances; ensure positivity and growth bound are justified.

### T5 Self‑similarity selects k = 1; golden ratio
- [ ] Connect Σ(k) minimality to the selection principle statement; document link to T4 canonical J.
- [ ] Optional: add stability of the φ fixed point under the recurrence and characterize convergence domain.

### T6 Minimal stable spatial dimension d = 3
- [ ] Keep `StableLinking` as a parameterized class but reduce placeholders:
  - [ ] Encode minimal invariants used (e.g., linking number properties) with typed statements.
  - [ ] Add references and a proof outline for Jordan (d=2), Alexander (d≥4), Hopf link (d=3).
- [ ] Strengthen `hopf_link_cost_lower_bound` to use J and show coherent growth with scale R ≥ 1.

### T7 Minimal recognition period T = 2^D; D=3 explicit
- [ ] Provide an explicit `[HasGrayCode D]` instance via an inductive Gray‑code generator.
- [ ] Strengthen `hypercube_minimal_period` to the exact equality: existence (Gray code) + minimality (cardinality) ⇒ period = 2^D.
- [ ] Keep D=3 explicit (`gray8`) and cross‑check adjacency proof.

### T8 Causality (max speed c = Lmin/τ0)
- [ ] Formalize nearest‑neighbor dynamics per atomic tick; define lattice metric.
- [ ] Prove light‑cone bound: positions reachable after n ticks lie within radius n·Lmin; deduce c.
- [ ] Connect to T7 (tick period) and T6 (spatial lattice) in the statement.

### Repo/tooling/infra
- [ ] Fix external build/toolchain issues (Lean 4.21 + mathlib/aesop/batteries/proofwidgets mismatches).
  - [ ] Pin versions in `lean-toolchain` and `lakefile.lean` consistently; run `lake update`.
  - [ ] Remove macOS resource files (`._*`) under `.lake/packages/**` to avoid non‑UTF‑8 errors.
- [ ] Add CI (build + lints) and a reproducible setup section in `README`.
- [ ] Extract large documentation blocks into `docs/` and keep Lean comments brief (author preference). [[memory:2494304]]
- [ ] Add a short "Eight‑theorem spine" overview doc linking each theorem to its Lean file.
- [ ] Add minimal test/examples (unit proofs) per theorem to guard regressions.

### Quick wins (high‑impact, low risk)
- [ ] Implement `[HasGrayCode D]` and prove `hypercube_minimal_period` exactly.
- [ ] Replace `Cost/Functional.cost_unique` with a stub that calls the Laurent route until the full proof is ready, avoiding heuristic equalities.
- [ ] Prove cone pointedness and antisymmetry in T1; this unlocks a credible uniqueness statement.


