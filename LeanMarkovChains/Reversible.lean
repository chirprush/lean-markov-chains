import Mathlib
import LeanMarkovChains.Basic
import LeanMarkovChains.StationaryDistribution
import LeanMarkovChains.Spectral

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

def IsReversible (M : MarkovChain α) (p : ProbDistribution α) :=
  ∀ x y, (p.π x) * (M.P x y) = (p.π y) * (M.P y x)

theorem IsReversible.has_stationary
  {M : MarkovChain α} {p : ProbDistribution α}
  (hRev : M.IsReversible p) :
  M.HasStationary p := by
  sorry

-- TODO: Make stuff like this more ergonomic. We should be able to do something
-- like M.IsReversible.convergence_bound
theorem IsReversible.convergence_bound
  {M : MarkovChain α} {p : ProbDistribution α}
  (hIrred : M.IsIrreducible) (hAper : M.IsAperiodic)
  (hRev : M.IsReversible p) :
  ∀ t > 0, ∀ x y, ∃ C > 0, |((M.P ^ t) x y) / (p.π y) - 1| ≤ C * (1 - M.SpectralGap) ^ t := by
  sorry

-- We need to define a new inner product, so we must create a new wrapper space
-- in Lean
-- In general this feels very hacky, so figure out how ergonomic this stuff is
-- later
-- structure PiSpace (α : Type u) [Fintype α] [DecidableEq α] (p : ProbDistribution α) where
-- (positive : ∀ i, p.π i > 0)
-- (v : α → ℝ)
--
-- variable (q : ProbDistribution α)
--
-- def PiSpace.equiv (h : ∀ i, q.π i > 0) : PiSpace α q ≃ (α → ℝ) where
--   toFun := PiSpace.v
--   invFun := fun v => { positive := h, v := v }
--   left_inv := fun _ => rfl
--   right_inv := fun _ => rfl
--
-- instance [h : Fact (∀ i, q.π i > 0)] : AddCommGroup (PiSpace α q) :=
--   (PiSpace.equiv q h.out).addCommGroup
--
-- noncomputable instance [h : Fact (∀ i, q.π i > 0)] : Module ℝ (PiSpace α q) :=
--   (PiSpace.equiv q h.out).module ℝ
--
-- noncomputable instance [h : Fact (∀ i, q.π i > 0)] : InnerProductSpace ℝ (PiSpace α q) :=
--   InnerProductSpace.ofCore {
--     inner := by sorry
--     conj_inner_symm := by sorry
--     re_inner_nonneg := by sorry
--     add_left := by sorry
--     smul_left := by sorry
--   }
-- ^ This is going to be a pain since I think we also need to instance
-- NormedAddCommGroup and NormedSpace ℝ but oh well

end MarkovChain
