import Neoplatonic.LTR.ComplexValuedObservableAlgebra
import Mathlib.Topology.Closure

/-!
# Involution and faithfulness for compact complex-valued observables

The full infinite Hilbert representation intertwines pointwise complex
conjugation and Hilbert adjoints. If the marked endpoints contain a
dense sequence, the representation of continuous complex functions
is faithful. These are the remaining star-algebra laws behind the
bundled C(X, ℂ) representation.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Complex conjugation of a continuous function is represented
by the actual Hilbert adjoint on the infinite direct sum. -/
theorem compactComplexObservablePi_star
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (a : X → ℂ) (ha : Continuous a) :
    star (compactComplexObservablePi left right a ha) =
      compactComplexObservablePi left right (fun x => star (a x)) ha.star := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (compactComplexObservablePi left right (fun x => star (a x)) ha.star)
    (compactComplexObservablePi left right a ha)).mpr
  intro ψ φ
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  change inner ℂ
      (complexValuedObservableBlock (star (a (left j))) (star (a (right j))) (ψ j))
      (φ j) =
    inner ℂ (ψ j)
      (complexValuedObservableBlock (a (left j)) (a (right j)) (φ j))
  rw [← complexValuedObservableBlock_star,
    ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left
    (complexValuedObservableBlock (a (left j)) (a (right j)))
    (φ j) (ψ j)

/-- A complex diagonal matrix vanishes exactly when its two
point-evaluation values vanish. -/
theorem complexValuedObservableMatrix_eq_zero_iff (a b : ℂ) :
    complexValuedObservableMatrix a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
    simp [complexValuedObservableMatrix] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    exact complexValuedObservableMatrix_zero

theorem complexValuedObservableBlock_eq_zero_iff (a b : ℂ) :
    complexValuedObservableBlock a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    apply (complexValuedObservableMatrix_eq_zero_iff a b).mp
    apply (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).injective
    simpa [complexValuedObservableBlock] using h
  · rintro ⟨rfl, rfl⟩
    exact complexValuedObservableBlock_zero

/-- The bounded global complex representation sees every endpoint. -/
theorem complexValuedPairCLM_eq_zero_values
    (left right : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j, ‖left j‖ ≤ M ∧ ‖right j‖ ≤ M)
    (hzero : complexValuedPairCLM left right M hM hbound = 0) :
    ∀ j, left j = 0 ∧ right j = 0 := by
  intro j
  have hblock : complexValuedObservableBlock (left j) (right j) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg
      (fun T : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert =>
        (T (lp.single 2 j v)) j) hzero
    simpa [complexValuedPairCLM_apply] using h
  exact (complexValuedObservableBlock_eq_zero_iff (left j) (right j)).mp hblock

/-- Continuous complex observables vanishing on a dense sequence vanish
everywhere, by closure of the zero locus. -/
theorem continuous_complex_eq_zero_of_dense_sequence
    {X : Type*} [TopologicalSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (a : X → ℂ) (ha : Continuous a)
    (hzero : ∀ n, a (q n) = 0) :
    ∀ x : X, a x = 0 := by
  let S : Set X := {x | a x = 0}
  have hclosed : IsClosed S := isClosed_eq ha continuous_const
  have hsub : Set.range q ⊆ S := by
    rintro x ⟨n, rfl⟩
    exact hzero n
  have hfull : Set.univ ⊆ S := by
    simpa only [hq.closure_eq] using closure_minimal hsub hclosed
  intro x
  exact hfull (Set.mem_univ x)

/-- The canonical complex C(X) Hilbert representation is faithful when
the marked endpoints include a dense countable sequence. -/
theorem compactComplexObservablePi_faithful
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hcover : ∀ n, ∃ j, left j = q n ∨ right j = q n)
    (a : X → ℂ) (ha : Continuous a)
    (hzero : compactComplexObservablePi left right a ha = 0) :
    ∀ x : X, a x = 0 := by
  have hend := complexValuedPairCLM_eq_zero_values
    (fun j => a (left j)) (fun j => a (right j))
    (compactComplexObservableBound a ha)
    (compactComplexObservableBound_nonneg a ha)
    (fun j => ⟨compactComplexObservableBound_apply a ha (left j),
      compactComplexObservableBound_apply a ha (right j)⟩)
    hzero
  apply continuous_complex_eq_zero_of_dense_sequence q hq a ha
  intro n
  obtain ⟨j, hl | hr⟩ := hcover n
  · simpa [hl] using (hend j).1
  · simpa [hr] using (hend j).2

end Neoplatonic.LTR
