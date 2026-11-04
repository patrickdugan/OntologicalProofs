import Neoplatonic.LTR.ManifestationMarkedBlocks
import Neoplatonic.LTR.ComplexObservableSeminorm
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# LTR-MAN-07: actual finite-rank compression of the Hilbert representation

For f ∈ C(X,ℂ), the existing compactComplexObservableStarAlgHom is the
block-diagonal operator with j-th block diag(f(left j), f(right j)).

Define the genuine orthogonal block cutoff P_J on H = ℓ²(ℕ,ℂ²),
with identity blocks for j < J and zero blocks afterward. Define
C_J(f) directly by the corresponding truncated two-point blocks.

The first theorem relates C_J(f) to P_J π(f) P_J. The finite-rank
certificate factors each surviving block through a genuine ℂ² space.

The norm-isometry on the m-sentence Boolean fragment is established
in the companion module after the generic operator identities.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Orthogonal block cutoff: the first J two-dimensional Hilbert
blocks are kept, and every block with index at least J is zeroed. -/
noncomputable def manifestationHilbertBlockProjection (J : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  lp.mapCLM 2
    (fun j => if j < J then
      (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)))
      else 0)
    1 (by
      intro j
      by_cases hj : j < J
      · simp [hj]
      · simp [hj])

/-- The actual operator cutoff has the expected coordinate action. -/
theorem manifestationHilbertBlockProjection_apply
    (J : ℕ) (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (manifestationHilbertBlockProjection J ψ) j =
      if j < J then ψ j else 0 := by
  change (if j < J then
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)))
    else 0) (ψ j) = _
  by_cases hj : j < J <;> simp [hj]

/-- A genuine bounded complex Hilbert operator whose surviving blocks
are the same diagonal operators as the global representation. -/
noncomputable def manifestationFiniteObservableCompression
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (J : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  lp.mapCLM 2
    (fun j => if j < J
      then complexValuedObservableBlock (f (left j)) (f (right j))
      else 0)
    ‖f‖
    (by
      intro j
      by_cases hj : j < J
      · simpa only [if_pos hj] using
          complexValuedObservableBlock_norm_le
            (f (left j)) (f (right j))
            ‖f‖ (norm_nonneg f)
            (f.norm_coe_le_norm (left j))
            (f.norm_coe_le_norm (right j))
      · simpa only [if_neg hj, norm_zero] using (norm_nonneg f))

/-- Truncation acts on each surviving block, and vanishes elsewhere. -/
theorem manifestationFiniteObservableCompression_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (J : ℕ)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (manifestationFiniteObservableCompression left right f J ψ) j =
      if j < J then
        complexValuedObservableBlock (f (left j)) (f (right j)) (ψ j)
      else 0 := by
  change (if j < J
    then complexValuedObservableBlock (f (left j)) (f (right j))
    else 0) (ψ j) = _
  by_cases hj : j < J <;> simp [hj]

/-- The truncation is exactly P_J π(f) P_J for the actual infinite
Hilbert-space continuous-function star-algebra representation. -/
theorem manifestationFiniteObservableCompression_eq_comp
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (J : ℕ) :
    manifestationFiniteObservableCompression left right f J =
      (manifestationHilbertBlockProjection J).comp
        (((compactComplexObservableStarAlgHom left right) f).comp
          (manifestationHilbertBlockProjection J)) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [manifestationFiniteObservableCompression_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    manifestationHilbertBlockProjection_apply]
  by_cases hj : j < J
  · rw [if_pos hj, compactComplexObservableStarAlgHom_apply,
      manifestationHilbertBlockProjection_apply, if_pos hj]
  · rw [if_neg hj, if_neg hj]

/-- The projection itself is idempotent on the genuine Hilbert sum. -/
theorem manifestationHilbertBlockProjection_idempotent (J : ℕ) :
    (manifestationHilbertBlockProjection J).comp
      (manifestationHilbertBlockProjection J) =
      manifestationHilbertBlockProjection J := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [ContinuousLinearMap.comp_apply,
    manifestationHilbertBlockProjection_apply,
    manifestationHilbertBlockProjection_apply]
  by_cases hj : j < J
  · simp [hj]
  · simp [hj]

/-- Finite-rank map supported at one two-point Hilbert block. -/
noncomputable def manifestationSingleObservableBlock
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (j : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  ((lp.singleContinuousLinearMap ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
        (complexValuedObservableBlock (f (left j)) (f (right j)))).comp
    (lp.evalCLM ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j)

/-- Each individual observable block factors through ℂ². -/
theorem manifestationSingleObservableBlock_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (j : ℕ) :
    IsCompactOperator (manifestationSingleObservableBlock left right f j) := by
  have hev : IsCompactOperator
      (lp.evalCLM ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  unfold manifestationSingleObservableBlock
  exact hev.clm_comp
    ((lp.singleContinuousLinearMap ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
        (complexValuedObservableBlock (f (left j)) (f (right j))))

/-- A finite sum of actual rank-at-most-two Hilbert operators. -/
noncomputable def manifestationFiniteObservableSum
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (J : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  ∑ j ∈ Finset.range J, manifestationSingleObservableBlock left right f j

/-- The finite sum is compact, since its summands factor through ℂ². -/
theorem manifestationFiniteObservableSum_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (J : ℕ) :
    IsCompactOperator (manifestationFiniteObservableSum left right f J) := by
  classical
  unfold manifestationFiniteObservableSum
  induction Finset.range J using Finset.induction_on with
  | empty =>
      simpa using (isCompactOperator_zero
        (M₁ := ComplexDiracBlockHilbert) (M₂ := ComplexDiracBlockHilbert))
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (manifestationSingleObservableBlock_compact left right f j).add ih

/-- Finite rank sum and cutoff have the same exact coordinate action. -/
theorem manifestationFiniteObservableSum_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (J : ℕ)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (manifestationFiniteObservableSum left right f J ψ) j =
      if j < J then
        complexValuedObservableBlock (f (left j)) (f (right j)) (ψ j)
      else 0 := by
  classical
  have hsum : manifestationFiniteObservableSum left right f J ψ =
      ∑ i ∈ Finset.range J,
        lp.single 2 i
          (complexValuedObservableBlock (f (left i)) (f (right i)) (ψ i)) := by
    simp [manifestationFiniteObservableSum, manifestationSingleObservableBlock,
      lp.evalCLM, lp.evalₗ] <;> rfl
  rw [hsum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  simp [Finset.sum_pi_single, Finset.mem_range]

/-- The compressed Hilbert representation equals its finite-rank sum. -/
theorem manifestationFiniteObservableCompression_eq_sum
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (J : ℕ) :
    manifestationFiniteObservableCompression left right f J =
      manifestationFiniteObservableSum left right f J := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [manifestationFiniteObservableCompression_apply,
    manifestationFiniteObservableSum_apply]

/-- A genuine finite-rank (compact) compression of the full
infinite-dimensional Hilbert representation. -/
theorem manifestationFiniteObservableCompression_compact
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (J : ℕ) :
    IsCompactOperator
      (manifestationFiniteObservableCompression left right f J) := by
  rw [manifestationFiniteObservableCompression_eq_sum]
  exact manifestationFiniteObservableSum_compact left right f J

/-- Uniform upper norm bound for the actual Hilbert compression. -/
theorem manifestationFiniteObservableCompression_norm_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ)) (J : ℕ) :
    ‖manifestationFiniteObservableCompression left right f J‖ ≤ ‖f‖ := by
  exact lp.norm_mapCLM_le 2
    (fun j => if j < J
      then complexValuedObservableBlock (f (left j)) (f (right j))
      else 0)
    (norm_nonneg f)
    (by
      intro j
      by_cases hj : j < J
      · simpa only [if_pos hj] using
          complexValuedObservableBlock_norm_le
            (f (left j)) (f (right j))
            ‖f‖ (norm_nonneg f)
            (f.norm_coe_le_norm (left j))
            (f.norm_coe_le_norm (right j))
      · simpa only [if_neg hj, norm_zero] using (norm_nonneg f))

end Neoplatonic.LTR
