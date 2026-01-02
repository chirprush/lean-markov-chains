import Mathlib
import Mathlib.Data.Nat.GCD.Basic
import LeanMarkovChains.Basic
import LeanMarkovChains.Irreducible

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

-- Mathlib.NumberTheory.FrobeniusNumber is very helpful here.
-- We eventually need Schur's theorem for proving that an irreducible, aperiodic
-- chain is ergodic
def PeriodStates (M : MarkovChain α) (x : α) :=
  { t : ℕ | 0 < t ∧ 0 < (M.P ^ t) x x }

noncomputable def Period (M : MarkovChain α) (x : α) :=
  Nat.setGcd (M.PeriodStates x)

lemma reachable_period_dvd {M : MarkovChain α} {x y : α}
  (hTo : M.Reachable x y) (hFrom : M.Reachable y x) :
  M.Period x ∣ M.Period y := by
  unfold MarkovChain.Period
  rw [Nat.dvd_setGcd_iff]
  intro m hm
  unfold MarkovChain.Reachable at hTo
  obtain ⟨i, hi⟩ := hTo
  unfold MarkovChain.Reachable at hFrom
  obtain ⟨j, hj⟩ := hFrom
  -- First, show that the gcd divides i + j so that it divides i + j + m
  have h1 : i + j ∈ M.PeriodStates x := by
    unfold MarkovChain.PeriodStates
    constructor
    · linarith
    · have hP : 0 < ((M.P ^ i) x y) * ((M.P ^ j) y x) := by
        exact mul_pos hi.right hj.right
      linarith [hP, MarkovChain.path_prob_le_all M i j x y x]
  rw [Nat.dvd_add_iff_right (Nat.setGcd_dvd_of_mem h1)]
  -- But then we can show that i + j + m is inside the set so we win
  have h2 : i + j + m ∈ M.PeriodStates x := by
    unfold MarkovChain.PeriodStates
    constructor
    · linarith
    · have hP1 : 0 < ((M.P ^ i) x y) * ((M.P ^ m) y y) := by
        unfold MarkovChain.PeriodStates at hm
        exact mul_pos hi.right hm.right
      have hP2 : 0 < (M.P ^ (i + m)) x y := by
        linarith [hP1, MarkovChain.path_prob_le_all M i m x y y]
      have hP3 : 0 < ((M.P ^ (i + m)) x y) * ((M.P ^ j) y x) := by
        exact mul_pos hP2 hj.right
      conv =>
        arg 2
        arg 2
        rw [add_right_comm]
      linarith [hP2, MarkovChain.path_prob_le_all M (i + m) j x y x]
  exact Nat.setGcd_dvd_of_mem h2

theorem irreducible_same_periods {M : MarkovChain α} (h : M.IsIrreducible) (x y : α) :
  M.Period x = M.Period y := by
  rw [MarkovChain.irreducible_iff_reachable] at h
  exact Nat.dvd_antisymm
    (MarkovChain.reachable_period_dvd (h x y) (h y x))
    (MarkovChain.reachable_period_dvd (h y x) (h x y))

noncomputable def IsAperiodic (M : MarkovChain α) :=
  ∀ x : α, M.Period x = 1

theorem IsAperiodic.irreducible_period_one_implies_aperiodic {M : MarkovChain α}
  (hIrred : M.IsIrreducible) (h : ∃ x, M.Period x = 1) :
  M.IsAperiodic := by
  obtain ⟨x, hx⟩ := h
  unfold MarkovChain.IsAperiodic
  intro y
  rw [← hx]
  exact MarkovChain.irreducible_same_periods hIrred y x

end MarkovChain
