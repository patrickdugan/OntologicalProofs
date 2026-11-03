import Neoplatonic.LTR.ComplexCompactRealAlgebra

/-!
# Self-adjointness of represented real continuous observables

A real-valued function gives a Hermitian two-point diagonal matrix.
On the infinite complex Hilbert direct sum, the corresponding
bounded multiplication operator is self-adjoint. This proves the
self-adjoint property for every real function in the compact-space
representation, complementing the verified unital additive and
multiplicative laws.
-/

namespace Neoplatonic.LTR

/-- The continuous complex-linear two-point observable block
associated with real endpoint values is self-adjoint. -/
theorem complexObservableBlock_isSelfAdjoint (a b : ℝ) :
    IsSelfAdjoint (complexObservableBlock a b) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  have h : ((complexDiagonalObservable a b).toEuclideanLin).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (complexDiagonalObservable_isHermitian a b)
  simpa only [complexObservableBlock,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using h

/-- Any continuous real function on compact X acts through a
self-adjoint bounded complex-linear operator on the actual
infinite Hilbert direct sum. -/
theorem compactRealObservablePi_isSelfAdjoint
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X)
    (a : X → ℝ) (ha : Continuous a) :
    IsSelfAdjoint (compactRealObservablePi left right a ha) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro ψ φ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  change inner ℂ
      (complexObservableBlock (a (left j)) (a (right j)) (ψ j))
      (φ j) =
    inner ℂ (ψ j)
      (complexObservableBlock (a (left j)) (a (right j)) (φ j))
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (complexObservableBlock_isSelfAdjoint (a (left j)) (a (right j))))
      (ψ j) (φ j)

end Neoplatonic.LTR
