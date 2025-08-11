/--
Axiom audit for key theorems. This file is for human/CI inspection only.
It emits the axiom dependencies of the core results to ensure we only rely
on Lean/Mathlib foundations (and clearly‑declared assumptions).
-/

import MetaPrinciple.Recognition.Meta
import MetaPrinciple.Foundations.T2_Atomicity
import MetaPrinciple.Foundations.T3_Continuity
import MetaPrinciple.LatticeFree

open MetaPrinciple

-- Print axiom dependencies in the messages view
#eval IO.println "Axiom audit:"
#print axioms MetaPrinciple.mp_holds
#print axioms MetaPrinciple.T2_atomicity
#print axioms MetaPrinciple.T3_continuity
#print axioms MetaPrinciple.LatticeFree.eight_tick_min


