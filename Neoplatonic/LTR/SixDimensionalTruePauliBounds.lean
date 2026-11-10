import Neoplatonic.LTR.TwoDimensionalCstarMatrixTransport
import Neoplatonic.LTR.SignedResidualTraceZero
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-70: unconditional six-dimensional residual Pauli inequalities

MAN-69 puts the genuine compressed Hamming coordinate operators into
the two-by-two C*-matrix algebra with simultaneous norm contractions.

The same matrix-to-Euclidean equivalence respects star and matrix trace;
an isometric change of basis preserves the trace of an endomorphism.
Combined with the zero residual trace from MAN-64, the matrices are
Hermitian and traceless. Therefore MAN-67 applies directly, giving
explicit plus/minus quadratic Pauli coefficient bounds for every
genuine six-dimensional extremal system with zero ambient traces.
-/

namespace Neoplatonic.LTR

private abbrev TwoEuclidean := EuclideanSpace ℂ (Fin 2)
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The inverse matrix-to-Euclidean-CLM equivalence agrees with
the conventional orthonormal-basis matrix representation. -/
theorem twoEuclideanCstarMatrix_eq_orthonormalMatrix
    (T : TwoEuclidean →L[ℂ] TwoEuclidean) :
    twoEuclideanCstarMatrix T =
      LinearMap.toMatrixOrthonormal
        (EuclideanSpace.basisFun (Fin 2) ℂ) T.toLinearMap := by
  rfl

/-- The C*-matrix representation preserves the trace of
the underlying bounded Euclidean Hilbert operator. -/
theorem twoEuclideanCstarMatrix_trace
    (T : TwoEuclidean →L[ℂ] TwoEuclidean) :
    (twoEuclideanCstarMatrix T).trace =
      LinearMap.trace ℂ TwoEuclidean T.toLinearMap := by
  rw [twoEuclideanCstarMatrix_eq_orthonormalMatrix]
  exact (LinearMap.trace_eq_matrix_trace ℂ
    (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis T.toLinearMap).symm

/-- The C*-matrix representation of a self-adjoint Euclidean
bounded operator is Hermitian. -/
theorem twoEuclideanCstarMatrix_isHermitian
    (T : TwoEuclidean →L[ℂ] TwoEuclidean)
    (hT : IsSelfAdjoint T) :
    (twoEuclideanCstarMatrix T).IsHermitian := by
  apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
  change star (twoEuclideanCstarMatrix T) =
    twoEuclideanCstarMatrix T
  have h := congrArg
    ((Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm) hT.star_eq
  simpa only [map_star, twoEuclideanCstarMatrix] using h

section ConcreteSixDimensionalResidual

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]

/-- The actual residual coordinate A is self-adjoint after
transport through the common orthonormal Hilbert basis. -/
theorem TwoDirectionExtremalSystem.sixDimEuclideanResidualA_selfAdjoint
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    IsSelfAdjoint (S.sixDimEuclideanResidualA hq hDim) := by
  let U := (S.sixDimResidualBasis hq hDim).repr
  have h := (S.residualA_symmetric.isSelfAdjoint).conj_adjoint
    (U : S.residual →L[ℂ] TwoEuclidean)
  simpa [TwoDirectionExtremalSystem.sixDimEuclideanResidualA,
    hilbertIsometricConjugate, U, ContinuousLinearMap.comp_assoc,
    LinearIsometryEquiv.adjoint_eq_symm] using h

theorem TwoDirectionExtremalSystem.sixDimEuclideanResidualB_selfAdjoint
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    IsSelfAdjoint (S.sixDimEuclideanResidualB hq hDim) := by
  let U := (S.sixDimResidualBasis hq hDim).repr
  have h := (S.residualB_symmetric.isSelfAdjoint).conj_adjoint
    (U : S.residual →L[ℂ] TwoEuclidean)
  simpa [TwoDirectionExtremalSystem.sixDimEuclideanResidualB,
    hilbertIsometricConjugate, U, ContinuousLinearMap.comp_assoc,
    LinearIsometryEquiv.adjoint_eq_symm] using h

/-- The Euclidean conjugate of a residual continuous linear map
has the same linear endomorphism trace. -/
theorem TwoDirectionExtremalSystem.sixDimEuclideanResidualA_trace
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    LinearMap.trace ℂ TwoEuclidean
      (S.sixDimEuclideanResidualA hq hDim).toLinearMap =
        LinearMap.trace ℂ S.residual S.residualA.toLinearMap := by
  let U := (S.sixDimResidualBasis hq hDim).repr
  have hmap :
      (S.sixDimEuclideanResidualA hq hDim).toLinearMap =
        U.toLinearEquiv.conj S.residualA.toLinearMap := by
    ext x
    rfl
  rw [hmap]
  exact LinearMap.trace_conj' S.residualA.toLinearMap U.toLinearEquiv

theorem TwoDirectionExtremalSystem.sixDimEuclideanResidualB_trace
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    LinearMap.trace ℂ TwoEuclidean
      (S.sixDimEuclideanResidualB hq hDim).toLinearMap =
        LinearMap.trace ℂ S.residual S.residualB.toLinearMap := by
  let U := (S.sixDimResidualBasis hq hDim).repr
  have hmap :
      (S.sixDimEuclideanResidualB hq hDim).toLinearMap =
        U.toLinearEquiv.conj S.residualB.toLinearMap := by
    ext x
    rfl
  rw [hmap]
  exact LinearMap.trace_conj' S.residualB.toLinearMap U.toLinearEquiv

/-- The actual compressed coordinate matrices are Hermitian. -/
theorem TwoDirectionExtremalSystem.sixDimCstarMatrices_hermitian
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    (S.sixDimCstarResidualMatrixA hq hDim).IsHermitian ∧
    (S.sixDimCstarResidualMatrixB hq hDim).IsHermitian := by
  exact ⟨twoEuclideanCstarMatrix_isHermitian _
      (S.sixDimEuclideanResidualA_selfAdjoint hq hDim),
    twoEuclideanCstarMatrix_isHermitian _
      (S.sixDimEuclideanResidualB_selfAdjoint hq hDim)⟩

/-- Ambient trace zero is retained by both concrete C*-matrices. -/
theorem TwoDirectionExtremalSystem.sixDimCstarMatrices_trace_zero
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6)
    (htrA : LinearMap.trace ℂ H S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ H S.B.toLinearMap = 0) :
    (S.sixDimCstarResidualMatrixA hq hDim).trace = 0 ∧
    (S.sixDimCstarResidualMatrixB hq hDim).trace = 0 := by
  constructor
  · change (twoEuclideanCstarMatrix
        (S.sixDimEuclideanResidualA hq hDim)).trace = 0
    rw [twoEuclideanCstarMatrix_trace,
      S.sixDimEuclideanResidualA_trace hq hDim]
    exact S.residualA_trace_zero hq htrA
  · change (twoEuclideanCstarMatrix
        (S.sixDimEuclideanResidualB hq hDim)).trace = 0
    rw [twoEuclideanCstarMatrix_trace,
      S.sixDimEuclideanResidualB_trace hq hDim]
    exact S.residualB_trace_zero hq htrB

/-- Every genuine six-dimensional Hamming residual has the
explicit Pauli coefficient inequalities, with no independent
matrix-norm or matrix-trace assumptions. -/
theorem TwoDirectionExtremalSystem.sixDim_truePauliCoefficientBounds
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6)
    (htrA : LinearMap.trace ℂ H S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ H S.B.toLinearMap = 0) :
    let MA := S.sixDimCstarResidualMatrixA hq hDim
    let MB := S.sixDimCstarResidualMatrixB hq hDim
    ‖pauliQuadratic MA + pauliQuadratic MB + pauliMixed MA MB‖ ≤ 1 ∧
    ‖pauliQuadratic MA + pauliQuadratic MB - pauliMixed MA MB‖ ≤ 1 := by
  dsimp
  obtain ⟨hHermA, hHermB⟩ := S.sixDimCstarMatrices_hermitian hq hDim
  obtain ⟨hTrA, hTrB⟩ :=
    S.sixDimCstarMatrices_trace_zero hq hDim htrA htrB
  obtain ⟨hPlus, hMinus⟩ := S.sixDimCstarResidual_contracts hq hDim
  exact twoDim_pauli_simultaneous_contraction_coefficients
    _ _ hHermA hHermB hTrA hTrB hPlus hMinus

end ConcreteSixDimensionalResidual
end Neoplatonic.LTR
