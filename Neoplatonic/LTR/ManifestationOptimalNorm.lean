import Neoplatonic.LTR.ManifestationOptimalCoordinates

/-!
# LTR-MAN-08B: Norm-exact scalar-coordinate compression

The sparse Hilbert projection keeps only the left scalar coordinate
in each of the 2^m selected Dirac blocks. It acts on the SAME
infinite-dimensional Hilbert representation already verified in MAN-07.

The compression acts on block j by diag(f(left j),0) when j is selected
and by zero otherwise. The selected left endpoints realize every
possible m-bit truth assignment, giving exact C*-norm preservation
on the entire m-proposition fragment.

This is a norm theorem about an actual bounded Hilbert operator.
The range-dimension (= 2^m) formalization is an additional obligation.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- A two-point left-coordinate sandwich retains exactly its first
complex diagonal entry. -/
theorem manifestationLeftBlock_sandwich (a b : ℂ) :
    (complexValuedObservableBlock 1 0).comp
      ((complexValuedObservableBlock a b).comp
        (complexValuedObservableBlock 1 0)) =
    complexValuedObservableBlock a 0 := by
  rw [complexValuedObservableBlock_mul a b 1 0]
  rw [complexValuedObservableBlock_mul 1 0 (a * 1) (b * 0)]
  simp

end Neoplatonic.LTR

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open scoped lp

/-- Sparse Hilbert compression of the full existing complex representation. -/
noncomputable def optimalManifestationCompressedOperator
    (m : ℕ) (f : C(T.CompleteType Empty, ℂ)) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  let P := optimalManifestationHilbertProjection m
  let π := compactComplexObservableStarAlgHom
    effectiveNullaryMarkedLeft effectiveNullaryMarkedRight
  P.comp ((π f).comp P)

/-- Exact action of the scalar-coordinate finite support on a full
Hilbert vector. -/
theorem optimalManifestationCompressedOperator_apply
    (m : ℕ) (f : C(T.CompleteType Empty, ℂ))
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (optimalManifestationCompressedOperator m f ψ) j =
      if j ∈ optimalManifestationBlockSet m
      then complexValuedObservableBlock (f (effectiveNullaryMarkedLeft j)) 0
        (ψ j)
      else 0 := by
  unfold optimalManifestationCompressedOperator
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    optimalManifestationHilbertProjection_apply]
  by_cases hj : j ∈ optimalManifestationBlockSet m
  · rw [if_pos hj, compactComplexObservableStarAlgHom_apply,
      optimalManifestationHilbertProjection_apply]
    simp only [if_pos hj]
    change ((complexValuedObservableBlock 1 0).comp
      ((complexValuedObservableBlock
        (f (effectiveNullaryMarkedLeft j))
        (f (effectiveNullaryMarkedRight j))).comp
        (complexValuedObservableBlock 1 0))) (ψ j) =
      complexValuedObservableBlock (f (effectiveNullaryMarkedLeft j)) 0
        (ψ j)
    rw [manifestationLeftBlock_sandwich]
  · simp [hj]

/-- The compressed map dominates the first complex scalar norm of
every selected block. -/
theorem optimalManifestationCompressedOperator_selected_lower
    (m : ℕ) (f : C(T.CompleteType Empty, ℂ))
    (j : ℕ) (hj : j ∈ optimalManifestationBlockSet m) :
    ‖f (effectiveNullaryMarkedLeft j)‖ ≤
      ‖optimalManifestationCompressedOperator m f‖ := by
  have hcoord : ∀ ψ : ComplexDiracBlockHilbert, ∀ k : ℕ,
      (optimalManifestationCompressedOperator m f ψ) k =
      (if k ∈ optimalManifestationBlockSet m then
          complexValuedObservableBlock (f (effectiveNullaryMarkedLeft k)) 0
        else 0) (ψ k) := by
    intro ψ k
    rw [optimalManifestationCompressedOperator_apply]
    by_cases hk : k ∈ optimalManifestationBlockSet m <;> simp [hk]
  have hblock := complexHilbertBlock_norm_le_operator
    (fun k => if k ∈ optimalManifestationBlockSet m then
      complexValuedObservableBlock (f (effectiveNullaryMarkedLeft k)) 0
      else 0)
    (optimalManifestationCompressedOperator m f) hcoord j
  calc
    ‖f (effectiveNullaryMarkedLeft j)‖ ≤
      ‖complexValuedObservableBlock
          (f (effectiveNullaryMarkedLeft j)) 0‖ :=
        complexValuedObservableBlock_norm_left_le _ _
    _ ≤ ‖optimalManifestationCompressedOperator m f‖ := by
      simpa only [if_pos hj] using hblock

/-- The exact m-fragment norm is recovered by the rank-one-per-pattern
Hilbert compression, even though the original representation has
infinitely many two-point blocks. -/
theorem optimalManifestationCompressedOperator_norm_eq
    (m : ℕ) (g : (Fin m → Bool) → ℂ) :
    ‖optimalManifestationCompressedOperator m
      (manifestationFragmentObservable m g)‖ =
      ‖manifestationFragmentObservable m g‖ := by
  let f := manifestationFragmentObservable m g
  let P := optimalManifestationHilbertProjection m
  let π := compactComplexObservableStarAlgHom
      effectiveNullaryMarkedLeft effectiveNullaryMarkedRight
  let C := optimalManifestationCompressedOperator m f
  have hp : ‖P‖ ≤ 1 := optimalManifestationHilbertProjection_norm_le_one m
  have hπ : ‖π f‖ = ‖f‖ :=
    effectiveNullary_infiniteHilbert_norm_eq f
  have hupper : ‖C‖ ≤ ‖f‖ := by
    change ‖P.comp ((π f).comp P)‖ ≤ ‖f‖
    calc
      ‖P.comp ((π f).comp P)‖ ≤ ‖P‖ * ‖(π f).comp P‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖P‖ * (‖π f‖ * ‖P‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg P)
      _ ≤ ‖f‖ := by
        rw [hπ]
        have hp2 : ‖P‖ * ‖P‖ ≤ 1 := by
          calc
            ‖P‖ * ‖P‖ ≤ ‖P‖ * 1 :=
              mul_le_mul_of_nonneg_left hp (norm_nonneg P)
            _ = ‖P‖ := mul_one _
            _ ≤ 1 := hp
        calc
          ‖P‖ * (‖f‖ * ‖P‖) =
              ‖f‖ * (‖P‖ * ‖P‖) := by ring
          _ ≤ ‖f‖ * 1 :=
            mul_le_mul_of_nonneg_left hp2 (norm_nonneg f)
          _ = ‖f‖ := mul_one _
  have hlower : ‖f‖ ≤ ‖C‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg C)).2
    intro x
    let bits := manifestationPrefix m x
    let j := optimalManifestationBlock m bits
    have hj : j ∈ optimalManifestationBlockSet m :=
      optimalManifestationBlock_mem m bits
    have hb : manifestationPrefix m (effectiveNullaryMarkedLeft j) =
        bits := optimalManifestationBlock_prefix m bits
    calc
      ‖f x‖ = ‖g bits‖ := rfl
      _ = ‖f (effectiveNullaryMarkedLeft j)‖ := by
        change ‖g bits‖ =
          ‖g (manifestationPrefix m (effectiveNullaryMarkedLeft j))‖
        rw [hb]
      _ ≤ ‖C‖ :=
        optimalManifestationCompressedOperator_selected_lower m f j hj
  exact le_antisymm hupper hlower

/-- The compression recovers the norm of the concrete
syntax-numbered spectral triple, using the exact same π. -/
theorem optimalManifestation_spectralTriple_norm_eq
    (m : ℕ) (g : (Fin m → Bool) → ℂ) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    let P := optimalManifestationHilbertProjection m
    let f := manifestationFragmentObservable m g
    ‖P.comp ((effectiveNullaryStoneSpectralTriple.representation f).comp P)‖ =
      ‖effectiveNullaryStoneSpectralTriple.representation f‖ := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  have hrepr (f : C(T.CompleteType Empty, ℂ)) :
      effectiveNullaryStoneSpectralTriple.representation f =
        (compactComplexObservableStarAlgHom
          effectiveNullaryMarkedLeft effectiveNullaryMarkedRight) f := by
    rw [effectiveNullaryStoneSpectralTriple_eq_explicit]
    rfl
  dsimp only
  rw [hrepr]
  change ‖optimalManifestationCompressedOperator m
    (manifestationFragmentObservable m g)‖ =
    ‖(compactComplexObservableStarAlgHom
      effectiveNullaryMarkedLeft effectiveNullaryMarkedRight)
      (manifestationFragmentObservable m g)‖
  rw [optimalManifestationCompressedOperator_norm_eq,
      effectiveNullary_infiniteHilbert_norm_eq]

end Neoplatonic.LTR.Nullary
