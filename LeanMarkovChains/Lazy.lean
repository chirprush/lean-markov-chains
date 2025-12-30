import Mathlib
import LeanMarkovChains.Basic
import LeanMarkovChains.Irreducible
import LeanMarkovChains.Period

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

noncomputable def LazyChain (M : MarkovChain α) : MarkovChain α :=
  { P := (M.P + 1) / 2, nonneg := by sorry, row_sum_one := by sorry }

theorem irreducible_lazy_irreducible {M : MarkovChain α}
  (hIrred : M.IsIrreducible) :
  (LazyChain M).IsIrreducible := by
  sorry

theorem lazy_aperiodic (M : MarkovChain α) : (LazyChain M).IsAperiodic := by
  sorry

end MarkovChain
