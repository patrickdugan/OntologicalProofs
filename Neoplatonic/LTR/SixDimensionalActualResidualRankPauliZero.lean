import Neoplatonic.LTR.SixDimensionalAmbientResidualRankTransport
import Neoplatonic.LTR.SixDimensionalAmbientPauliDefectNorm
import Neoplatonic.LTR.SixDimensionalSignedWitnessTraceEnergy
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# LTR-MAN-177: actual residual Pauli scalar vanishes under signed rank deficiency

The full 6D exact-Hamming extremal quartet from MAN-76/84
splits the true Euclidean Hilbert space into a four-dimensional
signed eigenspace and an orthogonal two-dimensional residual.

On the residual, the positive Hamming witness T=A+B has
  T² = µplus I,  µplus=q+r+c,
where q,r,c are the genuine traceless Hermitian Pauli coefficients
from the original 6x6 Dirac operator and its common Hilbert basis.

MAN-144 gives I-T²=(1-µplus) P_res on the full ambient Hilbert space.
MAN-176 transports that exact orthogonal projector to the
literal original six-coordinate matrix ring, where MAN-175
shows rank(T)≤4 implies µplus=0.

This module proves the complete original-coordinate result for
the positive signed witness. A first-bit truth translation
will transfer it to the negative witness under the
original m01=m10=1 multiplicity assumption of MAN-174.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The positive signed coordinate witness cannot carry a
nonzero residual Pauli scalar square if its original six-by-six
matrix has rank at most four. All residual data is selected from
the actual common labelled Hermitian Dirac operator. -/
theorem sixLabelled_exactHamming_plusRankLeFour_pauliScalar_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hRank : (labelledSquareA label D +
      labelledSquareB label D).rank ≤ 4) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
      S.A = sixLabelledAOperator label D ∧
      S.B = sixLabelledBOperator label D ∧
      pauliQuadratic (S.sixDimResidualMatrixA hq (by simp)) +
        pauliQuadratic (S.sixDimResidualMatrixB hq (by simp)) +
        pauliMixed (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp)) = 0 := by
  obtain ⟨S, hq, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  let M : TwoMat := S.sixDimResidualMatrixA hq (by simp)
  let N : TwoMat := S.sixDimResidualMatrixB hq (by simp)
  let mu : ℂ := pauliQuadratic M + pauliQuadratic N + pauliMixed M N
  let q : Fin 4 → SixH :=
    twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  let K : Submodule ℂ SixH :=
    (Submodule.span ℂ (Set.range q))ᗮ
  let P : SixH →L[ℂ] SixH := K.starProjection
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  have htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact (sixLabelled_operatorTrace_zero label D).1
  have htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact (sixLabelled_operatorTrace_zero label D).2
  have hMat : (M + N) * (M + N) = mu • (1 : TwoMat) := by
    have h := S.sixDimResidual_sum_square hq (by simp) htrA htrB
    change (M + N) * (M + N) =
      Matrix.diagonal (fun _ : Fin 2 => mu) at h
    calc
      (M + N) * (M + N) =
          Matrix.diagonal (fun _ : Fin 2 => mu) := h
      _ = mu • (1 : TwoMat) := by
        ext i j
        by_cases hij : i = j <;>
          simp [Matrix.diagonal_apply, Matrix.smul_apply,
            Matrix.one_apply, hij, smul_eq_mul]
  have hResScalar :
      (S.residualA + S.residualB) *
        (S.residualA + S.residualB) =
          mu • (1 : S.residual →L[ℂ] S.residual) :=
    S.residualPlus_scalarSquare_of_pauli hq mu hMat
  have hQuartet (i : Fin 4) :
      (S.A + S.B) ((S.A + S.B) (q i)) = q i :=
    S.plus_square_one_on_quartet i
  have hResPoint : ∀ x ∈ K,
      (S.A + S.B) ((S.A + S.B) x) = mu • x := by
    intro x hx
    let y : S.residual := ⟨x, hx⟩
    have hp : ((S.residualA + S.residualB) *
      (S.residualA + S.residualB)) y = mu • y := by
      rw [hResScalar]
      rfl
    have h := congrArg (fun z : S.residual => (z : SixH)) hp
    change (S.A + S.B) ((S.A + S.B) x) = mu • x at h
    exact h
  have hAmbient :
      (1 : SixH →L[ℂ] SixH) -
        (S.A + S.B) * (S.A + S.B) = (1 - mu) • P :=
    hilbert_square_defect_eq_residual_projection
      (S.A + S.B) q mu hQuartet hResPoint
  have hP : P * P = P := by
    exact K.isIdempotentElem_starProjection
  have hWMap :
      W.toEuclideanLin.toContinuousLinearMap = S.A + S.B := by
    have hmap : W.toEuclideanLin.toContinuousLinearMap =
        sixLabelledAOperator label D +
          sixLabelledBOperator label D := by
      change (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) W =
        (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
          (labelledSquareA label D) +
        (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
          (labelledSquareB label D)
      exact map_add
        (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareA label D) (labelledSquareB label D)
    rw [hmap, ← hA, ← hB]
  have hDefect :
      (1 : SixH →L[ℂ] SixH) -
        W.toEuclideanLin.toContinuousLinearMap *
          W.toEuclideanLin.toContinuousLinearMap =
            (1 - mu) • P := by
    rw [hWMap]
    exact hAmbient
  have hRankW : W.rank ≤ 4 := hRank
  have hmu : mu = 0 :=
    sixMatrix_rank_le_four_residualSquare_scalar_zero
      W P mu hRankW hP hDefect
  refine ⟨S, hq, hA, hB, ?_⟩
  change mu = 0
  exact hmu

end Neoplatonic.LTR
