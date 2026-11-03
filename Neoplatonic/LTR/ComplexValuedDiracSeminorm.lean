import Neoplatonic.LTR.ComplexValuedDiracCommutatorGlobal
import Neoplatonic.LTR.ComplexObservableSeminorm

/-!
# Optimal commutator seminorm for complex-valued marked observables

The Hilbert operator norm of a diagonal blockwise complex
commutator equals the least uniform bound on the edge gradients
|s_j| * ‖f(y_j)-f(x_j)‖. The lower bound follows from the
previously kernel-checked general norm-one Hilbert coordinate
insertion and evaluation theorem.
-/

namespace Neoplatonic.LTR

open scoped lp

theorem complexValuedPairCommutatorBlock_norm_le_global
    (mass scale : ℕ → ℝ) (left right : ℕ → ℂ)
    (L : ℝ) (hL : 0 ≤ L)
    (hEdge : ∀ j, |scale j| * ‖right j - left j‖ ≤ L)
    (j : ℕ) :
    ‖complexValuedPairCommutatorBlock mass scale left right j‖ ≤
      ‖complexValuedPairCommutatorCLM mass scale left right L hL hEdge‖ := by
  exact complexHilbertBlock_norm_le_operator
    (complexValuedPairCommutatorBlock mass scale left right)
    (complexValuedPairCommutatorCLM mass scale left right L hL hEdge)
    (complexValuedPairCommutatorCLM_apply mass scale left right L hL hEdge)
    j

theorem complexValuedPairCommutator_edge_le_norm
    (mass scale : ℕ → ℝ) (left right : ℕ → ℂ)
    (L : ℝ) (hL : 0 ≤ L)
    (hEdge : ∀ j, |scale j| * ‖right j - left j‖ ≤ L)
    (j : ℕ) :
    |scale j| * ‖right j - left j‖ ≤
      ‖complexValuedPairCommutatorCLM mass scale left right L hL hEdge‖ := by
  rw [← complexValuedPairCommutatorBlock_norm]
  exact complexValuedPairCommutatorBlock_norm_le_global
    mass scale left right L hL hEdge j

theorem complexValuedPairCommutatorCLM_eq_of_bounds
    (mass scale : ℕ → ℝ) (left right : ℕ → ℂ)
    (L M : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hEdgeL : ∀ j, |scale j| * ‖right j - left j‖ ≤ L)
    (hEdgeM : ∀ j, |scale j| * ‖right j - left j‖ ≤ M) :
    complexValuedPairCommutatorCLM mass scale left right L hL hEdgeL =
      complexValuedPairCommutatorCLM mass scale left right M hM hEdgeM := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [complexValuedPairCommutatorCLM_apply, complexValuedPairCommutatorCLM_apply]

/-- The exact operator norm of the bounded complex-valued global
commutator is the optimal marked-edge Lipschitz bound. -/
theorem complexValuedPairCommutator_norm_le_iff
    (mass scale : ℕ → ℝ) (left right : ℕ → ℂ)
    (L M : ℝ) (hL : 0 ≤ L)
    (hEdgeL : ∀ j, |scale j| * ‖right j - left j‖ ≤ L)
    (hM : 0 ≤ M) :
    ‖complexValuedPairCommutatorCLM mass scale left right L hL hEdgeL‖ ≤ M ↔
      ∀ j, |scale j| * ‖right j - left j‖ ≤ M := by
  constructor
  · intro h j
    exact (complexValuedPairCommutator_edge_le_norm
      mass scale left right L hL hEdgeL j).trans h
  · intro h
    rw [complexValuedPairCommutatorCLM_eq_of_bounds
      mass scale left right L M hL hM hEdgeL h]
    exact complexValuedPairCommutatorCLM_norm_le
      mass scale left right M hM h

end Neoplatonic.LTR
