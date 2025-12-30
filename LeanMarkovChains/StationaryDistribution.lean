import Mathlib
import LeanMarkovChains.Basic
import LeanMarkovChains.Irreducible
import LeanMarkovChains.Period

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

def HasStationary (M : MarkovChain α) (p : ProbDistribution α) :=
  M.evolve p = p

theorem irreducible_aperiodic_eventually_positive {M : MarkovChain α}
  (hIrred : M.IsIrreducible) (hAper : M.IsAperiodic) :
  ∃ T > 0, ∀ t ≥ T, (M.P ^ t).IsPositive := by
  sorry

theorem irreducible_unique_stationary {M : MarkovChain α} {p q : ProbDistribution α}
  (hIrred : M.IsIrreducible)
  (hp : M.HasStationary p) (hq : M.HasStationary q) :
  p.π = q.π := by
  sorry

theorem irreducible_positive_stationary {M : MarkovChain α} {p : ProbDistribution α}
  (hIrred : M.IsIrreducible) (hp : M.HasStationary p) :
  ∀ i, p.π i > 0 := by
  sorry

-- Perron-Frobenius (weak-form)
-- For a positive, stochastive matrix, there is a stochastic vector that is an
-- eigenvector for 1
-- Maybe restate this so it's more ergonomic in the following theorem that uses
-- it? Like maybe I wanto just bundle P into its own Markov Chain?
-- TODO: Look into this more once I have to prove this
lemma positive_exists_stochastic_eigenvector {P : Matrix α α ℝ}
  (hPos : P.IsPositive) (hRowSum : P.IsRowSumOne) :
  ∃ p : α → ℝ, (∀ i, p i ≥ 0) ∧ Matrix.vecMul p P = p := by
  sorry

theorem irreducible_aperiodic_exists_stationary {M : MarkovChain α}
  (hIrred : M.IsIrreducible) (hAper : M.IsAperiodic) :
  ∃ p, M.HasStationary p := by
  sorry

end MarkovChain
