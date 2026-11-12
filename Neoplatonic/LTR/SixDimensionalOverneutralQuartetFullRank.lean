import Neoplatonic.LTR.SixDimensionalOverneutralExchangeRank
import Neoplatonic.LTR.SixDimensionalOppositeCornerPauliBudget
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# LTR-MAN-185: four signed eigenvectors force original minus witness rank 4

MAN-184 gives rank(W) <= 2 + rank(Y) when QWQ=0, with C=I−Q
and Y=CWQ. MAN-174 proves rank(Wminus)<=4, rank(Cminus)=2
whenever m01=m10=1.

For every actual six-dimensional exact-Hamming Dirac representation,
the original extremal system has four orthonormal signed eigenvectors
of Wminus=A−B with squared eigenvalues one. Thus the four vectors
belong to the image of Wminus and force its rank at least four.
Combined with MAN-174, rank(Wminus)=4 and MAN-184's refined
rank gate gives rank(Yminus)=2.

No eigenbasis beyond the original signed quartet and no Pauli
near-saturation premise.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ
private abbrev SixH := EuclideanSpace ℂ (Fin 6)

/-- The literal finite complex matrix rank agrees with the
rank of its Euclidean Hilbert linear map in the original basis. -/
theorem sixMatrix_rank_eq_finrank_range_toEuclideanLin (W : SixMat) :
    W.rank = Module.finrank ℂ (LinearMap.range W.toEuclideanLin) := by
  have h := W.rank_eq_finrank_range_toLin
    (PiLp.basisFun (2 : ℝ≥0∞) ℂ (Fin 6))
    (PiLp.basisFun (2 : ℝ≥0∞) ℂ (Fin 6))
  change W.rank = Module.finrank ℂ
    (LinearMap.range
      ((Matrix.toLin (PiLp.basisFun (2 : ℝ≥0∞) ℂ (Fin 6))
        (PiLp.basisFun (2 : ℝ≥0∞) ℂ (Fin 6))) W))
  exact h

/-- Four orthonormal vectors fixed by the square of a 6D
complex matrix force its range to have dimension at least four. -/
theorem sixMatrix_rank_ge_four_of_orthonormal_square_one
    (W : SixMat) (q : Fin 4 → SixH)
    (hq : Orthonormal ℂ q)
    (hsq : ∀ i : Fin 4,
      W.toEuclideanLin (W.toEuclideanLin (q i)) = q i) :
    4 ≤ W.rank := by
  let T : SixH →ₗ[ℂ] SixH := W.toEuclideanLin
  have hSpan :
      Submodule.span ℂ (Set.range q) ≤ LinearMap.range T := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact ⟨T (q i), hsq i⟩
  have hFour :
      Module.finrank ℂ (Submodule.span ℂ (Set.range q)) = 4 := by
    simpa using finrank_span_eq_card hq.linearIndependent
  have hLower :
      4 ≤ Module.finrank ℂ (LinearMap.range T) := by
    rw [← hFour]
    exact Submodule.finrank_mono hSpan
  rw [sixMatrix_rank_eq_finrank_range_toEuclideanLin]
  exact hLower

/-- In every actual exact-Hamming six-dimensional Hermitian
Dirac chart, the original negative witness has at least four
linearly independent eigenvectors with eigenvalues of modulus one. -/
theorem sixLabelled_exactHamming_minusWitness_rank_ge_four
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    4 ≤ (labelledSquareA label D - labelledSquareB label D).rank := by
  obtain ⟨S, hq, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let q : Fin 4 → SixH :=
    twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  have hMap :
      W.toEuclideanLin.toContinuousLinearMap = S.A - S.B := by
    have hMatrix :
        W.toEuclideanLin.toContinuousLinearMap =
          sixLabelledAOperator label D -
            sixLabelledBOperator label D := by
      change (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareA label D - labelledSquareB label D) =
          (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
            (labelledSquareA label D) -
          (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
            (labelledSquareB label D)
      exact map_sub
        (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) _ _
    rw [hMatrix, ← hA, ← hB]
  have hSquare (i : Fin 4) :
      W.toEuclideanLin (W.toEuclideanLin (q i)) = q i := by
    change W.toEuclideanLin.toContinuousLinearMap
      (W.toEuclideanLin.toContinuousLinearMap (q i)) = q i
    rw [hMap]
    exact S.minus_square_one_on_quartet i
  exact sixMatrix_rank_ge_four_of_orthonormal_square_one
    W q hq hSquare

/-- The four signed eigenvectors and the overneutral zero block
pin the original negative witness rank exactly at four. -/
theorem sixLabelled_exactHamming_overneutral_minusWitness_rank_eq_four
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    (labelledSquareA label D -
      labelledSquareB label D).rank = 4 :=
  le_antisymm
    (sixLabelled_minusWitness_rank_le_four_of_neutralSingletons
      label D hm1 hm2)
    (sixLabelled_exactHamming_minusWitness_rank_ge_four label D hD hham)

/-- The original 01/10 active-to-00/11 neutral signed exchange
has rank exactly two, without Pauli saturation. -/
theorem sixLabelled_exactHamming_overneutral_minus_exchange_rank_two
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    let W := labelledSquareA label D - labelledSquareB label D
    let Q := sixTruthSectorProjection label squareMinusNeutral
    let C : SixMat := 1 - Q
    (C * W * Q).rank = 2 := by
  dsimp only
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  have hWH : W.IsHermitian :=
    sixLabelled_minusWitness_isHermitian label D hD
  have hQH : Q.IsHermitian :=
    sixTruthSectorProjection_isHermitian label squareMinusNeutral
  have hQQ : Q * W * Q = 0 :=
    sixTruthSectorProjection_W_zero
      label squareMinusNeutral W
      (sixLabelled_minusWitness_neutral_entry_zero label D)
  have hRank :
      W.rank = 4 :=
    sixLabelled_exactHamming_overneutral_minusWitness_rank_eq_four
      label D hD hham hm1 hm2
  have hC : (1 - Q : SixMat).rank = 2 := by
    rw [sixMinusNeutral_complement_eq_plusNeutral]
    rw [sixPlusNeutral_projection_rank_eq_fibreSum, hm1, hm2]
  exact sixMatrix_zeroNeutral_exchange_rank_two
    W Q hWH hQH hQQ hRank hC

end Neoplatonic.LTR
