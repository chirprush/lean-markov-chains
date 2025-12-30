import Mathlib

section

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

-- Main Stuff:
-- Markov chain structure
-- Properties: irreducible, ergodic, regular, reversible, aperiodic
-- Stationary distribution (existence, uniqueness)
--   Perron-Frobenius
-- Characterization of reversible chain convergence
-- Examples?

namespace Matrix

def IsPositive (P : Matrix α α ℝ) := ∀ x y : α, P x y > 0
def IsNonnegative (P : Matrix α α ℝ) := ∀ x y : α, P x y ≥ 0
def IsRowSumOne (P : Matrix α α ℝ) := ∀ x : α, ∑ y : α, P x y = 1
def IsStochastic (P : Matrix α α ℝ) := P.IsNonnegative ∧ P.IsRowSumOne

theorem IsPositive.mul_of_isStochastic {P Q : Matrix α α ℝ}
  (hP : P.IsPositive) (hQ : Q.IsStochastic) :
  Matrix.IsPositive (P • Q) :=
  sorry

-- TODO: Add some more theorems so that we know higher powers of transition matrices
-- are also stochastic

end Matrix


-- Given a suitable measure, one can drop the Fintype condition for α
structure MarkovChain (α : Type u) [Fintype α] [DecidableEq α] where
(P : Matrix α α ℝ)
(nonneg : P.IsNonnegative)
(row_sum_one : P.IsRowSumOne)

structure ProbDistribution (α : Type u) [Fintype α] [DecidableEq α] where
(π : α → ℝ)
(nonneg : ∀ i, π i ≥ 0)
(sum_one : ∑ i, π i = 1)

namespace MarkovChain

-- TODO: Maybe also add some information about nth iterates
def evolve (M : MarkovChain α) (p : ProbDistribution α) : ProbDistribution α :=
  { π := Matrix.vecMul p.π M.P, nonneg := by sorry, sum_one := by sorry }

theorem evolve_eq_matmul (M : MarkovChain α) (p : ProbDistribution α) :
  Matrix.vecMul p.π M.P = (M.evolve p).π := by
  unfold MarkovChain.evolve
  simp

theorem evolve_eq_weighted_sum (M : MarkovChain α) (p : ProbDistribution α) :
  ∀ i, (M.evolve p).π i = ∑ j, (M.P j i) * p.π j := by
  intro i
  rw [← MarkovChain.evolve_eq_matmul]
  unfold Matrix.vecMul
  unfold dotProduct
  simp_rw [mul_comm]

end MarkovChain

end
