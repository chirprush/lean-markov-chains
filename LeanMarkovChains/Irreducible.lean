import Mathlib
import LeanMarkovChains.Basic

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

def Reachable (M : MarkovChain α) (x y : α) :=
  ∃ k > 0, (M.P ^ k) x y > 0

def IsIrreducible (M : MarkovChain α) :=
  ∀ x y : α, ∃ k > 0, (M.P ^ k) x y > 0

theorem irreducible_iff_reachable (M : MarkovChain α) :
  M.IsIrreducible ↔ ∀ x y : α, M.Reachable x y := by
  rfl

theorem reachable_transitive {M : MarkovChain α} {x y z : α} (h1 : M.Reachable x y) (h2 : M.Reachable y z) :
  M.Reachable x z := by
  sorry

end MarkovChain
