import Neoplatonic.LTR.ComplexDenseConnesDistance
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compact continuous real observables in the complex Hilbert representation

For compact metric spaces, every continuous real observable is
uniformly bounded. Thus its two-point evaluations define a bounded
complex-linear representation on the infinite Hilbert direct sum,
without adding an external boundedness hypothesis.

The spectral triple's complex C(X) algebra, whose elements are
complex-valued functions, remains a further bundling step.
-/

namespace Neoplatonic.LTR

/-- On a compact space, any continuous real observable has a
nonnegative uniform bound for its absolute value. -/
theorem compactContinuousReal_has_bound
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (a : X → ℝ) (ha : Continuous a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : X, |a x| ≤ M := by
  obtain ⟨C, hC⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X)).exists_bound_of_continuousOn
      ha.continuousOn
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x
  have hx : ‖a x‖ ≤ C := hC x (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hx.trans (le_max_left C 0)

/-- Bounded complex Hilbert multiplication exists for every
continuous real function on a compact space, with its exact
two-point diagonal coordinate action. -/
theorem compactContinuousReal_observable_exists
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (a : X → ℝ) (ha : Continuous a) :
    ∃ (M : ℝ) (hM : 0 ≤ M)
      (hBound : ∀ j : ℕ, |a (left j)| ≤ M ∧ |a (right j)| ≤ M),
      ∃ π : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert,
        ∀ (ψ : ComplexDiracBlockHilbert) (j : ℕ),
          (π ψ) j =
            complexObservableBlock (a (left j)) (a (right j)) (ψ j) := by
  obtain ⟨M, hM, hAll⟩ := compactContinuousReal_has_bound a ha
  have hBound : ∀ j : ℕ, |a (left j)| ≤ M ∧ |a (right j)| ≤ M := by
    intro j
    exact ⟨hAll (left j), hAll (right j)⟩
  refine ⟨M, hM, hBound,
    complexPairObservableCLM (fun j => a (left j)) (fun j => a (right j))
      M hM hBound, ?_⟩
  intro ψ j
  exact complexPairObservableCLM_apply
    (fun j => a (left j)) (fun j => a (right j))
    M hM hBound ψ j

end Neoplatonic.LTR
