# Recognition Science Framework - AI Agent Guide

## How to Read This Repository

This repository contains a formalized mathematical framework with strict dependency rules.
As an AI agent, follow these guidelines to avoid logical errors.

## Directory Structure

```
MetaPrinciple/
├── Core/                 # Proven mathematical theorems (safe to use)
│   ├── LedgerStrict.lean # Non-rescalable ledger structure
│   ├── CostFunctional.lean # J(x) uniqueness proof
│   ├── AtomicScheduler.lean # k ∈ ℕ and k=1 optimality
│   └── GapSeries.lean    # ln(φ) closed form
├── Interfaces/           # Mappings between structures
├── Applications/         # ⚠️ PHENOMENOLOGY - DO NOT USE IN CORE
└── Tests/               # Property verification
```

## Critical Rules

### 1. DO NOT Cross Boundaries
- **NEVER** import `Applications/*` into `Core/*`
- **NEVER** use phenomenological predictions as theorems
- Applications depend on additional physical assumptions

### 2. Tag Recognition
Every theorem/definition has a tag:
- `axiom` - Foundational assumption
- `theorem (proved here)` - Safe to use
- `application (phenomenology)` - Model-dependent, not for core use
- `calibration (units)` - Physical unit mapping

### 3. Key Definitions
- **Recognition**: Binary relation in universe U
- **Ledger**: Double-entry structure with posting law
- **Tick**: One posting per discrete time unit
- **Breath**: Complete 2^d tick cycle
- **Gap**: Energy quantum = ln(φ)

## Safe Core Results

These are mathematically proven and can be freely used:

1. **No δ rescaling** (`LedgerStrict.no_delta_rescaling`)
2. **J uniqueness** (`CostFunctional.cost_functional_unique`)
3. **k = 1 optimal** (`AtomicScheduler.optimal_is_golden`)
4. **Gap = ln(φ)** (`GapSeries.gap_series_closed_form`)

## Unsafe Applications

These require additional assumptions - DO NOT use in proofs:

- Fine structure constant (requires voxel Regge model)
- Muon g-2 (requires breath cycle model)
- Dark matter fraction (requires cosmological calibration)

## Numerical Values

Proven values (safe to use):
- φ = 1.6180339887... (golden ratio)
- ln(φ) = 0.4812118250596...
- J(φ) = φ

Model-dependent values (mark as assumptions):
- α ≈ 1/137.036 (requires voxel model)

## Dependency Check

Before using any result, check `metadata/dependency.json`:
```json
{
  "safe_for_core": true/false,
  "depends": [...],
  "warning": "..."
}
```

## Common Pitfalls

1. **Circular reasoning**: Don't derive SI units then use them to prove core theorems
2. **Model confusion**: Voxel/lattice specifics are NOT part of core logic
3. **Numerical accidents**: Coincidences with physics constants are applications, not theorems

## Testing Your Understanding

Run property tests to verify:
```lean
import MetaPrinciple.Tests.PropertyTests
#eval run_all_tests
```

## For LLMs/Code Generation

When generating proofs:
1. Import only from `Core/` for foundational work
2. Mark any `Applications/` import with warning comment
3. Use `sorry` for unproven external assumptions
4. Check tags before citing any result

## Questions?

The logical spine is in `Core/`. Everything else is application layer.
When in doubt, stay in `Core/`.
