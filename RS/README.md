# Recognition Science - Minimal Kernel

This directory contains the minimal, bulletproof kernel for Recognition Science, designed to be:
- **Stable**: Fixed type signatures that won't change
- **Modular**: Axioms can be replaced with proofs without breaking dependencies
- **AI-robust**: Clear names, no hidden parameters, composable imports

## File Structure

### `Core.lean` - The Kernel
The absolute minimal set of definitions and axioms:

1. **Recognition Structure** (§2.1)
   - `RecognitionStructure`: MP + composability + well-foundedness
   - Proven: Meta-principle holds trivially

2. **Ledger** (§2.2) 
   - `Ledger`: Double-entry + positivity + conservation
   - `ledger_necessity_unique`: Existence & uniqueness (axiom)

3. **Cost Functional** (§2.3)
   - `J(x) = (x + x⁻¹)/2`: The canonical cost
   - `AdmissibleCost`: Symmetry + normalization + finiteness
   - `unique_cost_functional`: J is unique (axiom)
   - Proven: J is admissible

4. **Golden Ratio** (§3)
   - `φ = (1 + √5)/2`
   - Proven: `φ = 1 + 1/φ` fixed point
   - `k_eq_one`: Countability forces k=1 (axiom)

5. **Eight-Tick Cycle** (Appendix)
   - `EightTick.Walk`: Periodic complete walk on cube
   - `eight_tick_minimal`: Period = 8 (axiom)

6. **Gap Series**
   - `gapCoeff`: Coefficients (-1)^(m+1)/(m φ^m)
   - `gap_generating_closed_form`: Sums to log(1 + z/φ) (axiom)
   - Proven: At z=1, sum = log φ

### `Cost.lean` - Uniqueness Proof Strategy
Shows how to replace the `unique_cost_functional` axiom:
- Laurent expansion for symmetric functions
- Boundedness kills higher-order terms
- Normalization fixes coefficient = 1/2

### `Hypercube.lean` - Eight-Tick Proof
Concrete Gray code construction:
- `grayCode`: Explicit 8-vertex Hamiltonian cycle
- `grayWalk`: The concrete walk with period 8
- Pigeonhole argument for minimality

### `GapSeries.lean` - Gap Coefficients
Properties and convergence:
- Alternating series with decay 1/(m φ^m)
- Tail bounds
- Connection to ledger corrections

### `Tests.lean` - Verification
Numerical sanity checks:
- `J(2) = 5/4`
- `φ² = φ + 1`
- Gray walk period = 8
- Lists all axioms needing proofs

## Usage for AI Agents

```lean
import RS.Core

-- All downstream code uses stable names
example : RS.J 1 = 1 := RS.J_norm1

-- Create structures using the API
def MyLedger (M : RS.RecognitionStructure) : Type := 
  RS.Ledger M
```

## Axioms to Prove (in order of tractability)

1. **`eight_tick_minimal`** ✓ (easiest)
   - Gray code exists (done)
   - Pigeonhole for minimality (sketched)

2. **`k_eq_one`** (moderate)
   - Integer posting constraint
   - Cost monotonicity in k

3. **`unique_cost_functional`** (moderate)
   - Laurent expansion (sketched)
   - Growth analysis (sketched)

4. **`gap_generating_closed_form`** (standard)
   - Taylor series of log(1 + z/φ)

5. **`ledger_necessity_unique`** (algebraic)
   - Free abelian group construction
   - Order-isomorphism uniqueness

## Key Design Principles

1. **No Breaking Changes**: When replacing axiom with theorem, signature stays identical
2. **Explicit Hypotheses**: Every assumption is visible in the type
3. **Stable Names**: Use `RS.` prefix for all references
4. **Modular Proofs**: Each axiom can be tackled independently

## Quick Checks

```lean
#check RS.RecognitionStructure  -- Type u → Type u
#check RS.Ledger                -- RecognitionStructure → Type v
#check RS.J                      -- ℝ → ℝ
#check RS.φ                      -- ℝ (≈ 1.618...)
#check RS.eight_tick_minimal    -- ∀ w : Walk, w.T = 8
```

## Next Steps

1. Complete pigeonhole proof in `Hypercube.lean`
2. Add Laurent expansion details in `Cost.lean`
3. Prove `k_eq_one` using cost monotonicity
4. Connect to physics applications once kernel is solid
