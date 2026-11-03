import Neoplatonic.LTR.ComplexValuedObservableBlock
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Complex-valued observables on the infinite Dirac Hilbert sum

For uniformly bounded complex endpoint sequences, the diagonal
Euclidean complex-linear blocks act by a bounded map on
H = ℓ²(ℕ, ℂ²). Continuous complex-valued functions on compact X
are uniformly bounded, giving a canonical representation on H.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- A bounded complex two-point observable on the infinite Hilbert space. -/
noncomputable def complexValuedPairCLM
    (left right : ℕ → ℂ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ j, ‖left j‖ ≤ M ∧ ‖right j‖ ≤ M) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  lp.mapCLM 2
    (fun j => complexValuedObservableBlock (left j) (right j))
    hM
    (fun j => complexValuedObservableBlock_norm_le
      (left j) (right j) M hM (hbound j).1 (hbound j).2)

theorem complexValuedPairCLM_apply
    (left right : ℕ → ℂ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ j, ‖left j‖ ≤ M ∧ ‖right j‖ ≤ M)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (complexValuedPairCLM left right M hM hbound ψ) j =
      complexValuedObservableBlock (left j) (right j) (ψ j) := by
  change complexValuedObservableBlock (left j) (right j) (ψ j) = _
  rfl

theorem complexValuedPairCLM_norm_le
    (left right : ℕ → ℂ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ j, ‖left j‖ ≤ M ∧ ‖right j‖ ≤ M) :
    ‖complexValuedPairCLM left right M hM hbound‖ ≤ M :=
  lp.norm_mapCLM_le 2
    (fun j => complexValuedObservableBlock (left j) (right j))
    hM
    (fun j => complexValuedObservableBlock_norm_le
      (left j) (right j) M hM (hbound j).1 (hbound j).2)

/-- Continuous complex functions on compact spaces admit a
nonnegative uniform bound on the complex absolute value. -/
theorem compactContinuousComplex_has_bound
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (a : X → ℂ) (ha : Continuous a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : X, ‖a x‖ ≤ M := by
  obtain ⟨C, hC⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set X)).exists_bound_of_continuousOn
      ha.continuousOn
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x
  exact (hC x (Set.mem_univ x)).trans (le_max_left C 0)

/-- A canonical nonnegative bound used to construct the complex
Hilbert representation of each compact continuous function. -/
noncomputable def compactComplexObservableBound
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (a : X → ℂ) (ha : Continuous a) : ℝ :=
  Classical.choose (compactContinuousComplex_has_bound a ha)

theorem compactComplexObservableBound_nonneg
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (a : X → ℂ) (ha : Continuous a) :
    0 ≤ compactComplexObservableBound a ha :=
  (Classical.choose_spec (compactContinuousComplex_has_bound a ha)).1

theorem compactComplexObservableBound_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (a : X → ℂ) (ha : Continuous a) (x : X) :
    ‖a x‖ ≤ compactComplexObservableBound a ha :=
  (Classical.choose_spec (compactContinuousComplex_has_bound a ha)).2 x

/-- Continuous complex observables on compact X act by genuine bounded
complex-linear multiplication operators on ℓ²(ℕ,ℂ²). -/
noncomputable def compactComplexObservablePi
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (a : X → ℂ) (ha : Continuous a) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  complexValuedPairCLM
    (fun j => a (left j)) (fun j => a (right j))
    (compactComplexObservableBound a ha)
    (compactComplexObservableBound_nonneg a ha)
    (fun j => ⟨compactComplexObservableBound_apply a ha (left j),
      compactComplexObservableBound_apply a ha (right j)⟩)

/-- Exact coordinatewise action of the bounded complex function. -/
theorem compactComplexObservablePi_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (a : X → ℂ) (ha : Continuous a)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (compactComplexObservablePi left right a ha ψ) j =
      complexValuedObservableBlock (a (left j)) (a (right j)) (ψ j) := by
  exact complexValuedPairCLM_apply
    (fun j => a (left j)) (fun j => a (right j))
    (compactComplexObservableBound a ha)
    (compactComplexObservableBound_nonneg a ha)
    (fun j => ⟨compactComplexObservableBound_apply a ha (left j),
      compactComplexObservableBound_apply a ha (right j)⟩)
    ψ j

end Neoplatonic.LTR
