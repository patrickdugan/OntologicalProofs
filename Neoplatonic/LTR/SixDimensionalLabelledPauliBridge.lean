import Neoplatonic.LTR.SixDimensionalLabelledWitnesses
import Neoplatonic.LTR.SixDimensionalMixedTraceBridge
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-76: actual labelled Dirac support constrains the Pauli Gram product

MAN-75 identifies the ambient trace of AB for a six-dimensional
graded extremal system with the residual Pauli mixed coefficient.
MAN-74 proves the trace vanishes for the *actual* labelled Dirac
coordinate commutators if the Dirac operator has no opposite-corner
couplings.

The MAN-76 witness bridge constructs an extremal system whose
operators equal those concrete matrix commutators exactly.
This module combines the two results: under the genuine dual unit
edge bounds, admissible opposite witnesses, and the opposite-corner
support condition, the real Pauli vectors of the compressed residual
are orthogonal.

No zero-product AB=0 premise is introduced. The hypothesis about
opposite-corner Dirac couplings remains explicit, and no general
six-dimensional exact-Hamming obstruction is claimed.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Trace of a concrete six-dimensional Hilbert matrix equals
the ordinary complex matrix trace. -/
theorem sixLabelled_trace_toEuclidean
    (M : SixMat) :
    LinearMap.trace ℂ SixH M.toEuclideanLin =
      M.trace := by
  change LinearMap.trace ℂ SixH (Matrix.toLpLin 2 2 M) = M.trace
  rw [Matrix.toLpLin_eq_toLin]
  exact Matrix.trace_toLin_eq M (PiLp.basisFun (2 : ℝ≥0∞) ℂ (Fin 6))

/-- The ambient product trace for the actual six-dimensional labelled
Dirac operators equals the complex trace of the matrix product. -/
theorem sixLabelled_ambientProduct_matrixTrace
    (label : Fin 6 → Fin 4) (D : SixMat) :
    LinearMap.trace ℂ SixH
      ((sixLabelledAOperator label D).toLinearMap *
        (sixLabelledBOperator label D).toLinearMap) =
      (labelledSquareA label D * labelledSquareB label D).trace := by
  let M := labelledSquareA label D
  let N := labelledSquareB label D
  have hmul : (M * N).toEuclideanLin =
      M.toEuclideanLin.comp N.toEuclideanLin :=
    Matrix.toLpLin_mul_same (p := (2 : ℝ≥0∞)) M N
  have hlin :
      (sixLabelledAOperator label D).toLinearMap *
        (sixLabelledBOperator label D).toLinearMap =
      (M * N).toEuclideanLin := by
    change M.toEuclideanLin.comp N.toEuclideanLin =
      (M * N).toEuclideanLin
    exact hmul.symm
  rw [hlin]
  exact sixLabelled_trace_toEuclidean (M * N)

/-- Both actual imaginary coordinate commutators have zero Hilbert
endomorphism trace in any six-dimensional labelled Dirac chart. -/
theorem sixLabelled_operatorTrace_zero
    (label : Fin 6 → Fin 4) (D : SixMat) :
    LinearMap.trace ℂ SixH
      (sixLabelledAOperator label D).toLinearMap = 0 ∧
    LinearMap.trace ℂ SixH
      (sixLabelledBOperator label D).toLinearMap = 0 := by
  constructor
  · change LinearMap.trace ℂ SixH
      (labelledSquareA label D).toEuclideanLin = 0
    rw [sixLabelled_trace_toEuclidean]
    exact labelledSquareA_trace_zero label D
  · change LinearMap.trace ℂ SixH
      (labelledSquareB label D).toEuclideanLin = 0
    rw [sixLabelled_trace_toEuclidean]
    exact labelledSquareB_trace_zero label D

/-- If a concrete labelled six-dimensional Dirac spectral system
has its actual coordinate operators A and B, the mixed Pauli
coefficient of its two-dimensional residual equals the true
matrix product trace. -/
theorem sixLabelled_extremal_pauliMixed_eq_matrixTrace
    (label : Fin 6 → Fin 4) (D : SixMat)
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hA : S.A = sixLabelledAOperator label D)
    (hB : S.B = sixLabelledBOperator label D) :
    pauliMixed (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp)) =
        (labelledSquareA label D * labelledSquareB label D).trace := by
  obtain ⟨htrA, htrB⟩ := sixLabelled_operatorTrace_zero label D
  have hta : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact htrA
  have htb : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact htrB
  have htrace := S.sixDim_ambientProduct_trace_eq_pauliMixed
    hq (by simp) hta htb
  calc
    pauliMixed (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp)) =
      LinearMap.trace ℂ SixH
        (S.A.toLinearMap * S.B.toLinearMap) := htrace.symm
    _ = (labelledSquareA label D * labelledSquareB label D).trace := by
      rw [hA, hB]
      exact sixLabelled_ambientProduct_matrixTrace label D

/-- With no opposite-truth-corner couplings, the true two-dimensional
residual Pauli coefficient vanishes. This is a spectral statement
about the same labelled Dirac matrix, not an unrelated abstract pair. -/
theorem sixLabelled_extremal_noOpposite_pauliMixed_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hA : S.A = sixLabelledAOperator label D)
    (hB : S.B = sixLabelledBOperator label D)
    (hopp : ∀ i j : Fin 6,
      squareTruthOpposite (label i) (label j) → D i j = 0) :
    pauliMixed (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp)) = 0 := by
  rw [sixLabelled_extremal_pauliMixed_eq_matrixTrace label D S hq hA hB]
  exact labelledSquare_crossTrace_zero_of_noOpposite label D hopp

/-- Exact labelled Connes dual unit-edge bounds and the two
opposite-corner witnesses construct a true extremal spectral pair.
Without opposite-corner Dirac couplings, its real Pauli triple
vectors are orthogonal, even when ordered products need not vanish. -/
theorem sixLabelled_witnessed_noOpposite_pauliOrthogonal
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hd01 : sixLabelledConnesDistance label D 0 1 = 1)
    (hd02 : sixLabelledConnesDistance label D 0 2 = 1)
    (hsum : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerSum‖ ≤ 1)
    (hdiff : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerDifference‖ ≤ 1)
    (hopp : ∀ i j : Fin 6,
      squareTruthOpposite (label i) (label j) → D i j = 0) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        pauliRealDot (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp)) = 0 := by
  obtain ⟨S, hq, hA, hB⟩ :=
    sixLabelled_exactEdges_witnessed_extremalSystem
      label D hD hd01 hd02 hsum hdiff
  refine ⟨S, hq, hA, hB, ?_⟩
  let M := S.sixDimResidualMatrixA hq (by simp)
  let N := S.sixDimResidualMatrixB hq (by simp)
  have hc : pauliMixed M N = 0 :=
    sixLabelled_extremal_noOpposite_pauliMixed_zero
      label D S hq hA hB hopp
  have hm : pauliRealMixed M N = 0 := by
    simp [pauliRealMixed, hc]
  have hdot := pauliRealMixed_eq_two_dot M N
    (S.sixDimResidualMatrixA_isHermitian hq (by simp))
    (S.sixDimResidualMatrixB_isHermitian hq (by simp))
  rw [hm] at hdot
  dsimp only [M, N] at *
  linarith

end Neoplatonic.LTR
