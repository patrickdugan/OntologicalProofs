import Neoplatonic.LTR.SixDimensionalActualMinusResidualRankZero
import Neoplatonic.LTR.SixDimensionalAmbientPauliDefectNorm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-179: zero Pauli scalar forces the full overneutral residual matrix to vanish

MAN-178 proves the original negative Hamming witness W-=A-B has rank at
most four when both 01/10 truth atoms are singleton. It then uses the
true six-coordinate complex Hilbert residual projection to prove that
the translated positive signed Pauli scalar mu=q+r+c is zero.

The actual residual matrix T=M+N in the translated chart is Hermitian
and traceless. MAN-66 gives T²=mu I. At mu=0, Hermitianity and the
faithfulness of the complex matrix C*-algebra force T=0.

Thus the *complete original negative signed residual block* vanishes,
in the same orthonormal residual basis as the initial Dirac matrix.
This holds for all Pauli overlaps with no near-saturation assumption.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- A Hermitian 2x2 complex matrix whose square is zero must
itself vanish. This uses the positive C*-Gram identity. -/
theorem sixMatrix_twoDim_hermitian_square_zero
    (T : TwoMat) (hT : T.IsHermitian)
    (hT2 : T * T = 0) : T = 0 := by
  apply Matrix.self_mul_conjTranspose_eq_zero.mp
  rw [hT.eq]
  exact hT2

/-- For the true translated six-dimensional Hamming extremal
system, the entire common residual *sum* matrix is zero when
the original neutral truth atoms 01 and 10 are singleton. -/
theorem sixLabelled_exactHamming_overneutral_translatedResidual_sum_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    let tau := twoBitSquareTranslation 1
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
      S.A = sixLabelledAOperator (tau ∘ label) D ∧
      S.B = sixLabelledBOperator (tau ∘ label) D ∧
      S.sixDimResidualMatrixA hq (by simp) +
        S.sixDimResidualMatrixB hq (by simp) = 0 := by
  dsimp only
  obtain ⟨S, hq, hA, hB, hMu⟩ :=
    sixLabelled_exactHamming_overneutral_minusResidualPauli_zero
      label D hD hham hm1 hm2
  let M : TwoMat := S.sixDimResidualMatrixA hq (by simp)
  let N : TwoMat := S.sixDimResidualMatrixB hq (by simp)
  let T : TwoMat := M + N
  have hM : M.IsHermitian :=
    S.sixDimResidualMatrixA_isHermitian hq (by simp)
  have hN : N.IsHermitian :=
    S.sixDimResidualMatrixB_isHermitian hq (by simp)
  have hT : T.IsHermitian := by
    change (M + N).conjTranspose = M + N
    rw [Matrix.conjTranspose_add, hM.eq, hN.eq]
  have htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact (sixLabelled_operatorTrace_zero (twoBitSquareTranslation 1 ∘ label) D).1
  have htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact (sixLabelled_operatorTrace_zero (twoBitSquareTranslation 1 ∘ label) D).2
  have hSq := S.sixDimResidual_sum_square hq (by simp) htrA htrB
  change T * T =
    Matrix.diagonal (fun _ : Fin 2 =>
      pauliQuadratic M + pauliQuadratic N + pauliMixed M N) at hSq
  have hMu' : pauliQuadratic M + pauliQuadratic N +
      pauliMixed M N = 0 := hMu
  have hT2 : T * T = 0 := by
    rw [hMu'] at hSq
    simpa using hSq
  have hZero : T = 0 :=
    sixMatrix_twoDim_hermitian_square_zero T hT hT2
  refine ⟨S, hq, hA, hB, ?_⟩
  change T = 0
  exact hZero

/-- The two actual translated residual Pauli matrices are
opposites, so their sum annihilates the full two-dimensional
orthogonal complement of the signed Hamming quartet. -/
theorem sixLabelled_exactHamming_overneutral_translatedResidual_opposites
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    let tau := twoBitSquareTranslation 1
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
      S.A = sixLabelledAOperator (tau ∘ label) D ∧
      S.B = sixLabelledBOperator (tau ∘ label) D ∧
      S.sixDimResidualMatrixA hq (by simp) =
        -S.sixDimResidualMatrixB hq (by simp) := by
  dsimp only
  obtain ⟨S, hq, hA, hB, hZero⟩ :=
    sixLabelled_exactHamming_overneutral_translatedResidual_sum_zero
      label D hD hham hm1 hm2
  refine ⟨S, hq, hA, hB, ?_⟩
  have hSub :
      S.sixDimResidualMatrixA hq (by simp) =
        S.sixDimResidualMatrixA hq (by simp) +
          S.sixDimResidualMatrixB hq (by simp) -
          S.sixDimResidualMatrixB hq (by simp) := by abel
  rw [hSub, hZero]
  simp

end Neoplatonic.LTR
