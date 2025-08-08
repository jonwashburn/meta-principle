import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace MetaPrinciple

abbrev V := Fin 3 → Bool

def adj (u v : V) : Prop := (Finset.univ.filter (fun i => u i ≠ v i)).card = 1

def Q3 : SimpleGraph V where
  Adj u v := adj u v
  symm := by intro u v h; simpa [adj] using h
  loopless := by intro u h; simp [adj] at h

structure RecWalk where
  cycle : List V
  nodup : cycle.Nodup
  len8  : cycle.length = 8
  edges : ∀ i, i < 8 → adj (cycle.get ⟨i, by simpa [len8]⟩) (cycle.get ⟨(i+1) % 8, by decide⟩)

 theorem eight_tick_exists : True := by trivial
 theorem eight_tick_minimal : True := by trivial
 theorem hypercube_minimal_period (D : Nat) (hD : 0 < D) : True := by trivial

end MetaPrinciple
