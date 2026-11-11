import Neoplatonic.LTR.SixDimensionalResidualDefectProjection
import Neoplatonic.LTR.SixDimensionalResidualScalarSquareLift
import Neoplatonic.LTR.SixDimensionalExactHammingPauliSaturation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-146: exact six-dimensional signed spectral defect from Pauli residual

The signed extremal quartet carries square-one eigenvalues of
the actual positive witness T=A+B. Its orthogonal two-dimensional
residual carries scalar square mu=q+r+c by MAN-66 and MAN-145,
in the genuine common complex Hilbert basis.

MAN-144 proves that I-T²=(1-mu)P_res in the ambient six-dimensional
Hilbert space. Its full operator norm equals |1-mu| because the
orthogonal residual has complex dimension two.

The matrix-to-Euclidean C*-isometry converts this identity into
the original arbitrary labelled complex 6x6 Dirac coordinates.
This does not require Pauli endpoint saturation.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The actual ambient signed Hilbert witness has a spectral
defect whose norm is exactly the residual Pauli scalar defect. -/
theorem TwoDirectionExtremalSystem.ambientPlus_defect_norm_eq_pauliScalar
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0) :
    let M := S.sixDimResidualMatrixA hq (by simp)
    let N := S.sixDimResidualMatrixB hq (by simp)
    ‖(1 : SixH →L[ℂ] SixH) - (S.A + S.B) * (S.A + S.B)‖ =
      ‖(1 : ℂ) - (pauliQuadratic M +
        pauliQuadratic N + pauliMixed M N)‖ := by
  dsimp only
  let q : Fin 4 → SixH :=
    twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  let M : TwoMat := S.sixDimResidualMatrixA hq (by simp)
  let N : TwoMat := S.sixDimResidualMatrixB hq (by simp)
  let mu : ℂ := pauliQuadratic M + pauliQuadratic N + pauliMixed M N
  change ‖(1 : SixH →L[ℂ] SixH) -
      (S.A + S.B) * (S.A + S.B)‖ = ‖(1 : ℂ) - mu‖
  have hMat : (M + N) * (M + N) = mu • (1 : TwoMat) := by
    have hSq := S.sixDimResidual_sum_square hq (by simp) htrA htrB
    change (M + N) * (M + N) =
      Matrix.diagonal (fun _ : Fin 2 => mu) at hSq
    calc
      (M + N) * (M + N) =
          Matrix.diagonal (fun _ : Fin 2 => mu) := hSq
      _ = mu • (1 : TwoMat) := by
        ext i j
        by_cases hij : i = j <;>
          simp [Matrix.diagonal_apply, Matrix.smul_apply,
            Matrix.one_apply, hij, smul_eq_mul]
  have hResScalar :
      (S.residualA + S.residualB) * (S.residualA + S.residualB) =
        mu • (1 : S.residual →L[ℂ] S.residual) :=
    S.residualPlus_scalarSquare_of_pauli hq mu hMat
  have hQuartet (i : Fin 4) :
      (S.A + S.B) ((S.A + S.B) (q i)) = q i :=
    S.plus_square_one_on_quartet i
  have hResPoint :
      ∀ x ∈ (Submodule.span ℂ (Set.range q))ᗮ,
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
  have hRank :
      Module.finrank ℂ (Submodule.span ℂ (Set.range q))ᗮ = 2 :=
    twoDirection_sixDim_residual_finrank q hq (by simp)
  have hResNonzero :
      (Submodule.span ℂ (Set.range q))ᗮ ≠ ⊥ := by
    intro hz
    rw [hz] at hRank
    simp at hRank
  exact hilbert_square_defect_norm_eq_residual_scalar
    (S.A + S.B) q mu hQuartet hResPoint hResNonzero

/-- The L2 operator norm of a six-coordinate matrix square
defect agrees with that of its concrete Euclidean Hilbert map. -/
theorem sixMatrix_squaredDefect_opNorm_transport
    (W : SixMat) :
    ‖(1 : SixMat) - W * W‖ =
      ‖(1 : SixH →L[ℂ] SixH) -
        W.toEuclideanLin.toContinuousLinearMap *
          W.toEuclideanLin.toContinuousLinearMap‖ := by
  rw [Matrix.cstar_norm_def]
  change ‖(Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
    ((1 : SixMat) - W * W)‖ = _
  rw [map_sub, map_one, map_mul]
  rfl

/-- Exact Hamming for the original arbitrary labelled complex
6x6 Hermitian Dirac chart gives an actual residual Pauli basis
whose scalar square determines the FULL ambient defect norm. -/
theorem sixLabelled_exactHamming_plusDefect_norm_eq_pauliScalar
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
      S.A = sixLabelledAOperator label D ∧
      S.B = sixLabelledBOperator label D ∧
      let W := labelledSquareA label D + labelledSquareB label D
      let M := S.sixDimResidualMatrixA hq (by simp)
      let N := S.sixDimResidualMatrixB hq (by simp)
      ‖(1 : SixMat) - W * W‖ =
        ‖(1 : ℂ) - (pauliQuadratic M +
          pauliQuadratic N + pauliMixed M N)‖ := by
  obtain ⟨S, hq, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  have htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact (sixLabelled_operatorTrace_zero label D).1
  have htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact (sixLabelled_operatorTrace_zero label D).2
  have hScalar :=
    S.ambientPlus_defect_norm_eq_pauliScalar hq htrA htrB
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  have hmap : W.toEuclideanLin.toContinuousLinearMap =
      sixLabelledAOperator label D + sixLabelledBOperator label D := by
    change (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) W =
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareA label D) +
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareB label D)
    exact map_add (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) _ _
  have hSmap : W.toEuclideanLin.toContinuousLinearMap = S.A + S.B := by
    rw [hmap, ← hA, ← hB]
  refine ⟨S, hq, hA, hB, ?_⟩
  change ‖(1 : SixMat) - W * W‖ =
    ‖(1 : ℂ) -
      (pauliQuadratic (S.sixDimResidualMatrixA hq (by simp)) +
        pauliQuadratic (S.sixDimResidualMatrixB hq (by simp)) +
        pauliMixed (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp)))‖
  rw [sixMatrix_squaredDefect_opNorm_transport, hSmap]
  exact hScalar

end Neoplatonic.LTR
