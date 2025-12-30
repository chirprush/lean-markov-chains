import Mathlib
import LeanMarkovChains.Basic
import LeanMarkovChains.Irreducible
import LeanMarkovChains.Period

universe u

variable {α : Type u} [Fintype α] [DecidableEq α]

namespace MarkovChain

-- Structure:
-- First we need to lift P to be complex -> this allows us to access complex
-- eigenvalues
-- Then, we are able to prove that any real eigenvalue of the lifted P is an
-- eigenvalue of P
-- Also we are able to translate in between left eigenvalues and right
-- eigenvalues through the char poly

noncomputable def ComplexP (M : MarkovChain α) : Matrix α α ℂ :=
    M.P.map (algebraMap ℝ ℂ)

noncomputable def Eigenvalues (M : MarkovChain α) : Multiset ℂ :=
    M.ComplexP.charpoly.roots

noncomputable def HasEigenvalue (M : MarkovChain α) (μ : ℂ) :=
    μ ∈ M.Eigenvalues

def HasLeftEigenvalue (M : MarkovChain α) (μ : ℂ) :=
    Module.End.HasEigenvalue (Matrix.toLin' M.ComplexP) μ

def HasRightEigenvalue (M : MarkovChain α) (μ : ℂ) :=
    Module.End.HasEigenvalue (Matrix.toLinearMapRight' M.ComplexP) μ

-- TODO: Maybe also some theorems relating the above definitions?

noncomputable def SpectralGap (M : MarkovChain α) : ℝ :=
    let magnitudes := M.Eigenvalues.toList.map (fun x => ‖x‖)
    let μ := (magnitudes.erase 1).max?.getD 0
    1 - μ

theorem left_eigenvalue_iff_right_eigenvalue (M : MarkovChain α) (μ : ℂ) :
    M.HasLeftEigenvalue μ ↔ M.HasRightEigenvalue μ := by
    sorry

theorem left_real_eigenvalue_iff_lifted_eigenvalue (M : MarkovChain α) (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLin' M.P) μ ↔ M.HasLeftEigenvalue μ := by
    sorry

theorem right_real_eigenvalue_iff_lifted_eigenvalue (M : MarkovChain α) (μ : ℝ) :
    Module.End.HasEigenvalue (Matrix.toLinearMapRight' M.P) μ ↔ M.HasRightEigenvalue μ := by
    sorry

theorem has_eigenvalue_one (M : MarkovChain α) : M.HasLeftEigenvalue 1 := by
    sorry

theorem eigenvalues_abs_bounded_one {M : MarkovChain α}
    (μ : ℂ) (h : M.HasEigenvalue μ) :
    ‖μ‖ ≤ 1 := by
    sorry

-- I think a bit of a hacky personal proof works for this
theorem irreducible_aperiodic_unique_max_eigenvalue {M : MarkovChain α}
    (hIrred : M.IsIrreducible) (hAper : M.IsAperiodic) :
    ∀ μ, M.HasEigenvalue μ ↔ μ = 1 ∨ ‖μ‖ < 1 := by
    sorry

end MarkovChain
