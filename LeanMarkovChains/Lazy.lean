import Mathlib
import LeanMarkovChains.Basic
import LeanMarkovChains.Irreducible
import LeanMarkovChains.Period

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

noncomputable def LazyChain (M : MarkovChain α) : MarkovChain α where
  P := (1/2 : ℝ) • (M.P + 1)
  nonneg := by
    unfold Matrix.IsNonnegative
    simp only [one_div, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, ge_iff_le, inv_pos,
      Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    intro x y
    apply add_nonneg
    · exact M.nonneg x y
    · by_cases h : x = y <;>
        simp [Matrix.one_apply, h]
  row_sum_one := by
    unfold Matrix.IsRowSumOne
    intro x
    simp only [one_div, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul, ← Finset.mul_sum]
    rw [inv_mul_eq_iff_eq_mul₀ (by norm_num),
      Finset.sum_add_distrib, M.row_sum_one, Matrix.IsRowSumOne.one]
    norm_num

theorem LazyChain.half_le_diagonal (M : MarkovChain α) (x : α) :
  1/2 ≤ (M.LazyChain).P x x := by
  unfold MarkovChain.LazyChain
  simp only [one_div, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply_eq, smul_eq_mul,
    inv_pos, Nat.ofNat_pos, le_mul_iff_one_le_right, le_add_iff_nonneg_left]
  exact M.nonneg x x

theorem LazyChain.from_irreducible {M : MarkovChain α}
  (hIrred : M.IsIrreducible) :
  (LazyChain M).IsIrreducible := by
  unfold MarkovChain.IsIrreducible
  unfold MarkovChain.IsIrreducible at hIrred
  have h : ∀ t : ℕ, ∀ x y, (M.P ^ t) x y ≤ ((M.P + (1 : Matrix α α ℝ)) ^ t) x y := by
    intro t
    induction t with
    | zero => simp
    | succ d hd =>
      simp only [pow_add, pow_one, Matrix.mul_apply]
      intro x y
      gcongr with u du
      · exact M.nonneg u y
      · linarith [hd x u, Matrix.IsNonnegative.pow M.nonneg (k := d) x u]
      · exact hd x u
      · simp only [Matrix.add_apply, le_add_iff_nonneg_right]
        exact Matrix.IsNonnegative.one u y
  intro x y
  obtain ⟨T, hT⟩ := hIrred x y
  use T
  constructor
  · exact hT.left
  · unfold MarkovChain.LazyChain
    simp only [one_div, smul_pow]
    simp only [inv_pow, Matrix.smul_apply, smul_eq_mul, inv_pos, Nat.ofNat_pos, pow_pos,
      mul_pos_iff_of_pos_left]
    linarith [h T x y, hT.right]

theorem LazyChain.aperiodic (M : MarkovChain α) : (LazyChain M).IsAperiodic := by
  unfold MarkovChain.IsAperiodic
  intro x
  unfold MarkovChain.Period
  have h : 1 ∈ M.LazyChain.PeriodStates x := by
    unfold MarkovChain.PeriodStates
    constructor
    · norm_num
    · simp only [pow_one]
      linarith [MarkovChain.LazyChain.half_le_diagonal M x]
  rw [← Nat.dvd_one]
  exact Nat.setGcd_dvd_of_mem h

end MarkovChain
