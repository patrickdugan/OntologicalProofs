import Neoplatonic.LTR.ManifestationFiniteRankCompression
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Norm-exact finite-rank Hilbert compression for a logical fragment

The finite block cutoff is the genuine operator P_J π(f) P_J.
At J(m), the first m sentence-truth coordinates are all represented
at the left endpoints of actual marked Dirac blocks.

The result combines a bound on the full operator with a lower bound
from the two-point block C*-norm. It establishes exactly

  ‖P_J π(f) P_J‖ = ‖π(f)‖ = ‖f‖

for every complex observable f factoring through the first m
independent truth bits, while P_J π(f) P_J has rank at most 2J.

This relies on the original faithful infinite marked representation,
and the newly proved finite-fragment covering theorem; no norm
preservation is claimed uniformly over ALL continuous functions
at a single finite truncation.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The complex two-point diagonal block sees its left endpoint
with full scalar norm. -/
theorem complexValuedObservableBlock_norm_left_le
    (a b : ℂ) :
    ‖a‖ ≤ ‖complexValuedObservableBlock a b‖ := by
  change ‖a‖ ≤ ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexValuedObservableMatrix a b)‖
  rw [Matrix.l2_opNorm_toEuclideanCLM,
    complexValuedObservableMatrix_diagonal, Matrix.l2_opNorm_diagonal]
  simpa using (norm_le_pi_norm
    (fun i : Fin 2 => if i = 0 then a else b) (0 : Fin 2))

/-- The finite compression has norm at least as large as any
included two-point block norm, on the infinite Hilbert space. -/
theorem manifestationFiniteObservableCompression_block_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ))
    (J j : ℕ) (hj : j < J) :
    ‖complexValuedObservableBlock (f (left j)) (f (right j))‖ ≤
      ‖manifestationFiniteObservableCompression left right f J‖ := by
  have hcoord :
      ∀ (ψ : ComplexDiracBlockHilbert) (k : ℕ),
      (manifestationFiniteObservableCompression left right f J ψ) k =
        (if k < J then
          complexValuedObservableBlock (f (left k)) (f (right k))
          else 0) (ψ k) := by
    intro ψ k
    rw [manifestationFiniteObservableCompression_apply]
    by_cases hk : k < J <;> simp [hk]
  have h := complexHilbertBlock_norm_le_operator
    (fun k => if k < J then
      complexValuedObservableBlock (f (left k)) (f (right k))
      else 0)
    (manifestationFiniteObservableCompression left right f J)
    hcoord j
  simpa only [if_pos hj] using h

end Neoplatonic.LTR

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open scoped lp

/-- At the certified marked-block cutoff, the actual finite-rank
Hilbert operator has the full norm of ANY m-fragment observable. -/
theorem effectiveNullary_finiteRank_fragment_norm_eq
    (m : ℕ) (g : (Fin m → Bool) → ℂ) :
    ‖manifestationFiniteObservableCompression
        effectiveNullaryMarkedLeft effectiveNullaryMarkedRight
        (manifestationFragmentObservable m g)
        (effectiveNullaryMarkedPrefixCutoff m)‖ =
      ‖manifestationFragmentObservable m g‖ := by
  let f := manifestationFragmentObservable m g
  let J := effectiveNullaryMarkedPrefixCutoff m
  let C := manifestationFiniteObservableCompression
    effectiveNullaryMarkedLeft effectiveNullaryMarkedRight f J
  have hupper : ‖C‖ ≤ ‖f‖ :=
    manifestationFiniteObservableCompression_norm_le
      effectiveNullaryMarkedLeft effectiveNullaryMarkedRight f J
  have hlower : ‖f‖ ≤ ‖C‖ := by
    apply (manifestationFragment_norm_le_iff_samples
      m J effectiveNullaryMarkedLeft
      (effectiveNullaryMarkedPrefixCutoff_covers m)
      g ‖C‖ (norm_nonneg C)).2
    intro i
    calc
      ‖g (manifestationPrefix m (effectiveNullaryMarkedLeft i.val))‖ =
          ‖f (effectiveNullaryMarkedLeft i.val)‖ := rfl
      _ ≤ ‖complexValuedObservableBlock
          (f (effectiveNullaryMarkedLeft i.val))
          (f (effectiveNullaryMarkedRight i.val))‖ :=
            complexValuedObservableBlock_norm_left_le _ _
      _ ≤ ‖C‖ := manifestationFiniteObservableCompression_block_le
            effectiveNullaryMarkedLeft effectiveNullaryMarkedRight
            f J i.val i.isLt
  exact le_antisymm hupper hlower

/-- The bounded infinite marked complex representation is genuinely
isometric because it is a faithful star algebra homomorphism. -/
theorem effectiveNullary_infiniteHilbert_norm_eq
    (f : C(T.CompleteType Empty, ℂ)) :
    ‖(compactComplexObservableStarAlgHom
      effectiveNullaryMarkedLeft effectiveNullaryMarkedRight) f‖ =
      ‖f‖ := by
  have hinj : Function.Injective
      (compactComplexObservableStarAlgHom
        effectiveNullaryMarkedLeft effectiveNullaryMarkedRight) :=
    compactComplexObservableStarAlgHom_injective
      effectiveNullaryDenseSeq effectiveNullaryDenseSeq_dense
      effectiveNullaryMarkedLeft effectiveNullaryMarkedRight
      effectiveNullaryMarked_endpointCover
  exact NonUnitalStarAlgHom.norm_map _ hinj f

/-- Equality of the norm of the finite-rank compression with
the norm of the original infinite Hilbert representation,
for the complete m-proposition Boolean fragment. -/
theorem effectiveNullary_finiteRank_vs_infinite_norm
    (m : ℕ) (g : (Fin m → Bool) → ℂ) :
    ‖manifestationFiniteObservableCompression
        effectiveNullaryMarkedLeft effectiveNullaryMarkedRight
        (manifestationFragmentObservable m g)
        (effectiveNullaryMarkedPrefixCutoff m)‖ =
      ‖(compactComplexObservableStarAlgHom
        effectiveNullaryMarkedLeft effectiveNullaryMarkedRight)
        (manifestationFragmentObservable m g)‖ := by
  rw [effectiveNullary_finiteRank_fragment_norm_eq,
    effectiveNullary_infiniteHilbert_norm_eq]

/-- The exact finite-rank compression identity is also the identity
for the original syntax-numbered spectral triple's actual representation. -/
theorem effectiveNullary_finiteRank_spectralTriple_identity
    (m : ℕ) (g : (Fin m → Bool) → ℂ) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    let J := effectiveNullaryMarkedPrefixCutoff m
    let P := manifestationHilbertBlockProjection J
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
  let J := effectiveNullaryMarkedPrefixCutoff m
  let P := manifestationHilbertBlockProjection J
  let f := manifestationFragmentObservable m g
  dsimp only
  rw [hrepr]
  rw [← manifestationFiniteObservableCompression_eq_comp]
  exact effectiveNullary_finiteRank_vs_infinite_norm m g

/-- Verified finite rank / compactness of the SAME compressed operator. -/
theorem effectiveNullary_finiteRank_spectralTriple_compact
    (m : ℕ) (g : (Fin m → Bool) → ℂ) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    let J := effectiveNullaryMarkedPrefixCutoff m
    let P := manifestationHilbertBlockProjection J
    let f := manifestationFragmentObservable m g
    IsCompactOperator
      (P.comp ((effectiveNullaryStoneSpectralTriple.representation f).comp P)) := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  have hrepr (f : C(T.CompleteType Empty, ℂ)) :
      effectiveNullaryStoneSpectralTriple.representation f =
        (compactComplexObservableStarAlgHom
          effectiveNullaryMarkedLeft effectiveNullaryMarkedRight) f := by
    rw [effectiveNullaryStoneSpectralTriple_eq_explicit]
    rfl
  let J := effectiveNullaryMarkedPrefixCutoff m
  let P := manifestationHilbertBlockProjection J
  let f := manifestationFragmentObservable m g
  dsimp only
  rw [hrepr, ← manifestationFiniteObservableCompression_eq_comp]
  exact manifestationFiniteObservableCompression_compact
    effectiveNullaryMarkedLeft effectiveNullaryMarkedRight f J

end Neoplatonic.LTR.Nullary
