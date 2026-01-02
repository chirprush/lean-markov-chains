import Mathlib
import LeanMarkovChains.Basic

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

def Reachable (M : MarkovChain α) (x y : α) :=
  ∃ k > 0, 0 < (M.P ^ k) x y

def IsIrreducible (M : MarkovChain α) :=
  ∀ x y : α, ∃ k > 0, 0 < (M.P ^ k) x y

theorem irreducible_iff_reachable (M : MarkovChain α) :
  M.IsIrreducible ↔ ∀ x y : α, M.Reachable x y := by
  rfl

theorem path_prob_le_all
  (M : MarkovChain α) (s t : ℕ) (x y z : α) :
  ((M.P ^ s) x y) * ((M.P ^ t) y z) ≤ (M.P ^ (s + t)) x z := by
  rw [pow_add, Matrix.mul_apply]
  have h1 : ∀ j, 0 ≤ (M.P ^ s) x j * (M.P ^ t) j z := by
    intro j
    apply mul_nonneg
    · exact (Matrix.IsNonnegative.pow M.nonneg) x j
    · exact (Matrix.IsNonnegative.pow M.nonneg) j z
  exact Finset.single_le_sum
    (f := fun j => (M.P ^ s) x j * (M.P ^ t) j z)
    (by intro i hi; simp_rw [h1])
    (Finset.mem_univ y)

theorem reachable_transitive
  {M : MarkovChain α} {x y z : α}
  (h1 : M.Reachable x y) (h2 : M.Reachable y z) :
  M.Reachable x z := by
  unfold MarkovChain.Reachable
  unfold MarkovChain.Reachable at h1
  unfold MarkovChain.Reachable at h2
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  use s + t
  constructor
  · exact add_pos hs.left ht.left
  · have h0 : 0 < (M.P ^ s) x y * (M.P ^ t) y z := by
      apply mul_pos hs.right ht.right
    linarith [h0, MarkovChain.path_prob_le_all M s t x y z]

end MarkovChain
