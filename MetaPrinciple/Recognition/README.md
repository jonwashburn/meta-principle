# Recognition Framework - Stable API

This directory contains the modular, bulletproof foundation for Recognition Science.

## Core Module (`Core.lean`)

The stable API with fixed type signatures that won't change:

- `MetaPrinciple` - No self-recognition of nothing
- `RecognitionStructure` - MP + composability + well-foundedness  
- `Ledger` - Double-entry + positivity + conservation
- `AdmissibleCost` & `J` - Cost functional characterization
- `φ` - Golden ratio and fixed point
- `Voxel` & `LedgerCompatibleWalk` - Eight-tick cycle

**Key Design**: All major theorems are currently `axiom`s with stable signatures.
As we formalize proofs, we replace `axiom` with `theorem` without breaking downstream code.

## Graph Module (`Graph.lean`)

Concrete implementation of the 3-cube:
- `CubeVertex` - Vectors of 3 booleans
- `Cube3` - SimpleGraph with Hamming distance adjacency
- `grayCode3` - Explicit Gray code construction
- `cube8Walk` - Concrete 8-tick Hamiltonian cycle

## Proof Plan (`ProofPlan.lean`)

Shows how each axiom will become a theorem:
1. `ledger_exists` → Construction with ℤ costs
2. `cost_uniqueness` → Laurent expansion + boundedness
3. `delta_not_rescalable` → Order automorphism analysis
4. `k_is_one` → Cost minimization proof
5. `eight_tick_minimal` → Parity argument on Q₃

## Usage

```lean
import MetaPrinciple.Recognition.Core

-- All downstream code uses stable names
example : Recognition.MetaPrinciple := Recognition.metaPrinciple_holds

-- Create structures using the API
def MyStructure : RecognitionStructure where
  U := MyType
  nothing := myNothing
  recognizes := myRelation
  MP := by ...
  comp := by ...
  wf := by ...
```

## Migration Strategy

1. **Current**: Use `Core.lean` with axioms
2. **Incremental**: Replace axioms in `Core.lean` with theorems from `ProofPlan.lean`
3. **No Breaking Changes**: Type signatures remain identical

## For AI Agents

- **Always import `Core.lean`** for stable types
- **Never depend on proof details** - only on theorem names
- **Use qualified names** like `Recognition.MetaPrinciple`
- **Check axiom status** with `#print axioms theorem_name`

## Quick Sanity Checks

```lean
#check Recognition.MetaPrinciple        -- Prop
#check Recognition.Ledger               -- Type → Type → Type
#check Recognition.J                    -- ℝ → ℝ  
#check Recognition.φ                    -- ℝ
#check Recognition.eight_tick_minimal   -- ∀ X : Voxel, ...
```

## Next Steps

1. Replace `ledger_exists` with construction
2. Formalize Laurent expansion for `cost_uniqueness`
3. Complete Gray code proof in `Graph.lean`
4. Add executable tests for sanity checking
