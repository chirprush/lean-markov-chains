import Mathlib
import LeanMarkovChains.Basic
import LeanMarkovChains.Irreducible

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

noncomputable def Period (M : MarkovChain α) (x : α) :=
  sInf { t : ℕ | t ≥ 1 ∧ (M.P ^ t) x x > 0 }

theorem irreducible_same_periods {M : MarkovChain α} (h : M.IsIrreducible) (x y : α) :
  M.Period x = M.Period y := by
  sorry

noncomputable def IsAperiodic (M : MarkovChain α) :=
  ∀ x : α, M.Period x = 1

theorem IsAperiodic.irreducible_period_one_implies_aperiodic {M : MarkovChain α}
  (hIrred : M.IsIrreducible) (h : ∃ x, M.Period x = 1) :
  M.IsAperiodic := by
  sorry

end MarkovChain
