
## T5: Instantiating a new cost via a log-model

To prove F = J on ℝ>0 for a new cost, pick a log-domain function `G : ℝ → ℝ` and set `F x := G (log x)`.
Prove:
- evenness: `G (-t) = G t`
- normalization: `G 0 = 0`
- cosh bounds:
  - `G t ≤ ((exp t + exp (-t)) / 2 - 1)`
  - `((exp t + exp (-t)) / 2 - 1) ≤ G t`

Then in Lean:

```lean
open IndisputableMonolith.Cost

instance : LogModel G where
  even_log := your_evenness
  base0 := your_base0
  upper_cosh := your_upper
  lower_cosh := your_lower

-- Conclude immediately: for x > 0, F_ofLog G x = Jcost x
#check T5_for_log_model (G := G)
```

This yields T5 on ℝ>0 for `F := G ∘ log`.
