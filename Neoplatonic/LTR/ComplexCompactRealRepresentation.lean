import Neoplatonic.LTR.ComplexCompactRealObservables
import Neoplatonic.LTR.ComplexDenseObservableFaithful

/-!
# Canonical complex Hilbert representation of compact real observables

Choose a uniform bound for each continuous real function on compact X.
The bound only witnesses continuity of the diagonal Hilbert operator:
its coordinate action is independent of the chosen cap.

The resulting representation respects multiplication and the unit.
It is faithful whenever the marked endpoints contain a dense
countable sequence. This formalizes the real self-adjoint part of
the future complex C(X) spectral representation.
-/

namespace Neoplatonic.LTR

/-- A chosen nonnegative uniform bound for any continuous real
observable on a compact space. -/
noncomputable def compactRealObservableBound
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (a : X → ℝ) (ha : Continuous a) : ℝ :=
  Classical.choose (compactContinuousReal_has_bound a ha)

theorem compactRealObservableBound_nonneg
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (a : X → ℝ) (ha : Continuous a) :
    0 ≤ compactRealObservableBound a ha :=
  (Classical.choose_spec (compactContinuousReal_has_bound a ha)).1

theorem compactRealObservableBound_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (a : X → ℝ) (ha : Continuous a) (x : X) :
    |a x| ≤ compactRealObservableBound a ha :=
  (Classical.choose_spec (compactContinuousReal_has_bound a ha)).2 x

/-- Canonical bounded multiplication operator associated with a
continuous real observable on compact X and a marked pair sequence. -/
noncomputable def compactRealObservablePi
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (a : X → ℝ) (ha : Continuous a) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  complexPairObservableCLM
    (fun j => a (left j)) (fun j => a (right j))
    (compactRealObservableBound a ha)
    (compactRealObservableBound_nonneg a ha)
    (fun j => ⟨compactRealObservableBound_apply a ha (left j),
      compactRealObservableBound_apply a ha (right j)⟩)

/-- Every coordinate of the canonical compact-space representation
is exactly the two-point observable matrix action. -/
theorem compactRealObservablePi_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (a : X → ℝ) (ha : Continuous a)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (compactRealObservablePi left right a ha ψ) j =
      complexObservableBlock (a (left j)) (a (right j)) (ψ j) := by
  exact complexPairObservableCLM_apply
    (fun j => a (left j)) (fun j => a (right j))
    (compactRealObservableBound a ha)
    (compactRealObservableBound_nonneg a ha)
    (fun j => ⟨compactRealObservableBound_apply a ha (left j),
      compactRealObservableBound_apply a ha (right j)⟩)
    ψ j

/-- The constant one function is represented by the identity map. -/
theorem compactRealObservablePi_one
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) :
    compactRealObservablePi left right (fun _ => 1) continuous_const =
      ContinuousLinearMap.id ℂ ComplexDiracBlockHilbert := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  calc
    (compactRealObservablePi left right (fun _ => 1)
        continuous_const ψ) j =
      complexObservableBlock 1 1 (ψ j) :=
        compactRealObservablePi_apply left right
          (fun _ => 1) continuous_const ψ j
    _ = ψ j := by rw [complexObservableBlock_one]; rfl
    _ = ((ContinuousLinearMap.id ℂ ComplexDiracBlockHilbert) ψ) j := rfl

/-- Pointwise multiplication of compact real observables becomes
composition of their complex-linear Hilbert representations. -/
theorem compactRealObservablePi_mul
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X)
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b) :
    compactRealObservablePi left right (fun x => a x * b x) (ha.mul hb) =
      (compactRealObservablePi left right a ha).comp
        (compactRealObservablePi left right b hb) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  have hblock := congrArg
    (fun T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
      T (ψ j))
    (complexObservableBlock_mul
      (a (left j)) (a (right j)) (b (left j)) (b (right j)))
  calc
    (compactRealObservablePi left right (fun x => a x * b x)
        (ha.mul hb) ψ) j =
      complexObservableBlock
        (a (left j) * b (left j))
        (a (right j) * b (right j)) (ψ j) :=
      compactRealObservablePi_apply
        left right (fun x => a x * b x) (ha.mul hb) ψ j
    _ = complexObservableBlock (a (left j)) (a (right j))
        (complexObservableBlock (b (left j)) (b (right j)) (ψ j)) := by
      simpa only [ContinuousLinearMap.comp_apply] using hblock.symm
    _ = (((compactRealObservablePi left right a ha).comp
          (compactRealObservablePi left right b hb)) ψ) j := by
      rw [ContinuousLinearMap.comp_apply,
        compactRealObservablePi_apply, compactRealObservablePi_apply]

/-- Dense marked endpoints make the canonical compact continuous real
observable representation faithful. -/
theorem compactRealObservablePi_faithful
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hcover : ∀ n, ∃ j, left j = q n ∨ right j = q n)
    (a : X → ℝ) (ha : Continuous a)
    (hzero : compactRealObservablePi left right a ha = 0) :
    ∀ x : X, a x = 0 := by
  exact complexDenseObservable_faithful q hq left right hcover a ha
    (compactRealObservableBound a ha)
    (compactRealObservableBound_nonneg a ha)
    (fun j => ⟨compactRealObservableBound_apply a ha (left j),
      compactRealObservableBound_apply a ha (right j)⟩)
    hzero

end Neoplatonic.LTR
