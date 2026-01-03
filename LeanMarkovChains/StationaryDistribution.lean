import Mathlib
import LeanMarkovChains.Basic
import LeanMarkovChains.Irreducible
import LeanMarkovChains.Period

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

def HasStationary (M : MarkovChain α) (p : ProbDistribution α) :=
  M.evolve p = p

theorem HasStationary.dist_eq_matmul {M : MarkovChain α} {p : ProbDistribution α}
  (hp : M.HasStationary p) :
  Matrix.vecMul p.π M.P = p.π := by
  unfold MarkovChain.HasStationary at hp
  unfold MarkovChain.evolve at hp
  nth_rw 2 [← hp]

theorem HasStationary.dist_eq_weighted_sum {M : MarkovChain α} {p : ProbDistribution α} {i : α}
  (hp : M.HasStationary p) :
  ∑ j, (M.P j i) * (p.π j) = p.π i := by
  unfold MarkovChain.HasStationary at hp
  rw [← MarkovChain.evolve_eq_weighted_sum, hp]

theorem stationary_pow {M : MarkovChain α} {p : ProbDistribution α} {k : ℕ}
  (hp : M.HasStationary p) :
  Matrix.vecMul p.π (M.P ^ k) = p.π := by
  induction k with
  | zero => simp
  | succ t ht =>
    simp only [pow_add, pow_one, ← Matrix.vecMul_vecMul]
    rw [ht]
    exact MarkovChain.HasStationary.dist_eq_matmul hp

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
  ∀ i, 0 < p.π i := by
  intro i
  obtain ⟨x, hx⟩ := p.has_pos_entry
  obtain ⟨k, hk⟩ := hIrred x i
  rw [← MarkovChain.stationary_pow hp (k := k)]
  simp only [Matrix.vecMul, dotProduct]
  -- Because x gets shadowed
  change 0 < ∑ y, (p.π y) * ((M.P ^ k) y i)
  have h1 : 0 < (p.π x) * ((M.P ^ k) x i) := by
    apply mul_pos hx hk.right
  have h2 : (p.π x) * ((M.P ^ k) x i) ≤ ∑ y, (p.π y) * ((M.P ^ k) y i) := by
    refine Finset.single_le_sum (f := fun y => (p.π y) * ((M.P ^ k) y i)) ?_ ?_
    · intro u hu
      simp only
      apply mul_nonneg (p.nonneg u) (Matrix.IsNonnegative.pow M.nonneg u i)
    · simp
  linarith [h1, h2]

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
