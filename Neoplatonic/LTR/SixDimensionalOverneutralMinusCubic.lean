import Neoplatonic.LTR.SixDimensionalOverneutralResidualMatrixZero
import Neoplatonic.LTR.SixDimensionalAmbientResidualRankTransport
import Neoplatonic.LTR.SixDimensionalSignedBitFlipTransport
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-180: a cubic polynomial for the true overneutral signed Hamming witness

MAN-179 certifies that if 01 and 10 are singleton truth fibres in a
faithful six-dimensional exact-Hamming chart, the entire translated
residual matrix for Wplus'=-Wminus vanishes.

The positive signed quartet spans four actual ±1 eigendirections,
while the common two-dimensional orthogonal residual is annihilated.
Hence its full Hilbert square is the projection onto the quartet
span: Wplus'²=I-P_res. MAN-176 transports the genuine orthogonal
projection into the original 6×6 matrix coordinates.

The resulting original negative signed witness has an idempotent
matrix square Wminus⁴=Wminus². Hermitianity forces the stronger
cubic identity Wminus³=Wminus by the finite matrix C*-Gram theorem.

Thus the entire true witness spectrum lies in {-1,0,+1}, with
no Pauli saturation or near-half hypothesis. The polynomial is the
next input for excluding the remaining 01↔10 opposite Dirac block.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The complement of an idempotent complex matrix is also
idempotent. -/
theorem sixMatrix_complement_projection_idempotent
    (P : SixMat) (hP : P * P = P) :
    (1 - P : SixMat) * (1 - P) = 1 - P := by
  calc
    (1 - P : SixMat) * (1 - P) = 1 - P - P + P * P := by
      noncomm_ring
    _ = 1 - P := by rw [hP]; abel

/-- In a complex C*-matrix algebra, a Hermitian matrix with
idempotent square obeys its cubic spectral polynomial. -/
theorem sixMatrix_hermitian_square_idempotent_cubic
    (W : SixMat) (hWH : W.IsHermitian)
    (hSq : (W * W) * (W * W) = W * W) :
    W * W * W = W := by
  let Z : SixMat := W * W * W - W
  have hZH : Z.IsHermitian := by
    change (W * W * W - W).conjTranspose = W * W * W - W
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hWH.eq]
    noncomm_ring
  have hW6 :
      (W * W) * (W * W) * (W * W) = W * W := by
    rw [hSq, hSq]
  have hZ2 : Z * Z = 0 := by
    change (W * W * W - W) * (W * W * W - W) = 0
    calc
      (W * W * W - W) * (W * W * W - W) =
          (W * W) * (W * W) * (W * W) -
          (W * W) * (W * W) -
          (W * W) * (W * W) + W * W := by noncomm_ring
      _ = 0 := by rw [hW6, hSq]; abel
  have hGram : Z * Z.conjTranspose = 0 := by
    rw [hZH.eq]
    exact hZ2
  have hZ : Z = 0 :=
    Matrix.self_mul_conjTranspose_eq_zero.mp hGram
  change W * W * W - W = 0 at hZ
  exact sub_eq_zero.mp hZ

/-- MAN-179's complete translated residual zero identity makes
the literal original 6D matrix square of Wplus' idempotent. -/
theorem sixLabelled_exactHamming_overneutral_translatedPlus_square_idempotent
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    let tau := twoBitSquareTranslation 1
    let W := labelledSquareA (tau ∘ label) D +
      labelledSquareB (tau ∘ label) D
    (W * W) * (W * W) = W * W := by
  dsimp only
  let tau := twoBitSquareTranslation 1
  let W : SixMat := labelledSquareA (tau ∘ label) D +
    labelledSquareB (tau ∘ label) D
  obtain ⟨S, hq, hA, hB, hResZero⟩ :=
    sixLabelled_exactHamming_overneutral_translatedResidual_sum_zero
      label D hD hham hm1 hm2
  let M : TwoMat := S.sixDimResidualMatrixA hq (by simp)
  let N : TwoMat := S.sixDimResidualMatrixB hq (by simp)
  let q : Fin 4 → SixH :=
    twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  let K : Submodule ℂ SixH :=
    (Submodule.span ℂ (Set.range q))ᗮ
  let P : SixH →L[ℂ] SixH := K.starProjection
  have hResMat : M + N = 0 := hResZero
  have hMat : (M + N) * (M + N) = (0 : ℂ) • (1 : TwoMat) := by
    rw [hResMat]
    simp
  have hResSquare :
      (S.residualA + S.residualB) *
        (S.residualA + S.residualB) = 0 := by
    have h := S.residualPlus_scalarSquare_of_pauli hq 0 hMat
    simpa using h
  have hQuartet (i : Fin 4) :
      (S.A + S.B) ((S.A + S.B) (q i)) = q i :=
    S.plus_square_one_on_quartet i
  have hResPoint : ∀ x ∈ K,
      (S.A + S.B) ((S.A + S.B) x) = (0 : SixH) := by
    intro x hx
    let y : S.residual := ⟨x, hx⟩
    have hp : ((S.residualA + S.residualB) *
        (S.residualA + S.residualB)) y = (0 : S.residual) := by
      rw [hResSquare]
      rfl
    have h := congrArg (fun z : S.residual => (z : SixH)) hp
    change (S.A + S.B) ((S.A + S.B) x) = (0 : SixH) at h
    exact h
  have hAmbient :
      (1 : SixH →L[ℂ] SixH) -
        (S.A + S.B) * (S.A + S.B) = P := by
    have h := hilbert_square_defect_eq_residual_projection
      (S.A + S.B) q 0 hQuartet hResPoint
    simpa [P] using h
  have hProj : P * P = P := K.isIdempotentElem_starProjection
  let F := Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)
  let PM : SixMat := F.symm P
  have hPM : PM * PM = PM :=
    sixMatrix_residualProjection_transport_idempotent P hProj
  have hMap :
      W.toEuclideanLin.toContinuousLinearMap = S.A + S.B := by
    have hAdd : W.toEuclideanLin.toContinuousLinearMap =
        sixLabelledAOperator (tau ∘ label) D +
          sixLabelledBOperator (tau ∘ label) D := by
      change F W = F (labelledSquareA (tau ∘ label) D) +
        F (labelledSquareB (tau ∘ label) D)
      exact map_add F _ _
    rw [hAdd, ← hA, ← hB]
  have hDefect :
      (1 : SixH →L[ℂ] SixH) -
        W.toEuclideanLin.toContinuousLinearMap *
          W.toEuclideanLin.toContinuousLinearMap = P := by
    rw [hMap]
    exact hAmbient
  have hSqM : W * W = 1 - PM := by
    have h := sixMatrix_residualScalarSquare_transport W P 0
      (by simpa using hDefect)
    simpa using h
  change (W * W) * (W * W) = W * W
  rw [hSqM]
  exact sixMatrix_complement_projection_idempotent PM hPM

/-- With singleton 01/10 truth fibres, the original negative
six-dimensional signed Hamming commutator has an idempotent
square even in the interior Pauli-overlap region. -/
theorem sixLabelled_exactHamming_overneutral_minus_square_idempotent
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    let W := labelledSquareA label D - labelledSquareB label D
    (W * W) * (W * W) = W * W := by
  dsimp only
  have hTrans :=
    sixLabelled_exactHamming_overneutral_translatedPlus_square_idempotent
      label D hD hham hm1 hm2
  dsimp only at hTrans
  rw [sixLabelled_plusWitness_translationOne_eq_negMinus] at hTrans
  simpa only [neg_mul, mul_neg, neg_neg] using hTrans

/-- The original negative signed Dirac witness obeys its
cubic spectral polynomial on the entire 6D Hilbert space. -/
theorem sixLabelled_exactHamming_overneutral_minus_cubic
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    let W := labelledSquareA label D - labelledSquareB label D
    W * W * W = W := by
  dsimp only
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  have hH : W.IsHermitian :=
    sixLabelled_minusWitness_isHermitian label D hD
  have hSq := sixLabelled_exactHamming_overneutral_minus_square_idempotent
    label D hD hham hm1 hm2
  change (W * W) * (W * W) = W * W at hSq
  exact sixMatrix_hermitian_square_idempotent_cubic W hH hSq

end Neoplatonic.LTR
