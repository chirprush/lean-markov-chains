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

-- theorem IsPositive.mul_of_isStochastic {P Q : Matrix α α ℝ}
--   (hP : P.IsPositive) (hQ : Q.IsStochastic) :
--   Matrix.IsPositive (P • Q) :=
--   sorry

-- theorem IsStochastic.mul_of_isStochastic {P Q : Matrix α α ℝ}
--   (hP : P.IsStochastic) (hQ : Q.IsStochastic) :
--   (P * Q).IsStochastic := by
--   sorry

theorem IsNonnegative.pow {P : Matrix α α ℝ} {k : ℕ}
  (hP : P.IsNonnegative) :
  (P ^ k).IsNonnegative := by
  induction k with
  | zero =>
    simp only [pow_zero]
    unfold Matrix.IsNonnegative
    intro x y
    by_cases h : x = y <;>
    · simp [Matrix.one_apply, h]
  | succ d hd =>
    rw [pow_add, pow_one]
    unfold Matrix.IsNonnegative
    intro x y
    rw [Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · unfold Matrix.IsNonnegative at hd
      exact hd x i
    · unfold Matrix.IsNonnegative at hP
      exact hP i y

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
{
  π := Matrix.vecMul p.π M.P
  nonneg := by
    intro i
    unfold Matrix.vecMul dotProduct
    simp only [ge_iff_le]
    apply Finset.sum_nonneg
    intro x hx
    apply mul_nonneg
    · exact p.nonneg x
    · exact M.nonneg x i
  sum_one := by
    unfold Matrix.vecMul dotProduct
    simp only
    rw [Finset.sum_comm]
    conv =>
      lhs
      arg 2
      ext y
      rw [← Finset.mul_sum, M.row_sum_one]
      simp
    rw [p.sum_one]
}

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
