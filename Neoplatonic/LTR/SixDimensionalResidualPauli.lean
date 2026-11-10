import Neoplatonic.LTR.SignedResidualTraceZero
import Neoplatonic.LTR.TwoDimensionalPauliResidual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# LTR-MAN-65: actual 6D compressed coordinate matrices in Pauli normal form

MAN-60 compresses the two signed Hamming coordinate operators to the
invariant residual Hilbert subspace. MAN-59 gives residual dimension 2
when the ambient dimension is 6. MAN-64 proves that both compressed
operators have trace zero whenever the ambient commutators do.

Choose a genuine residual orthonormal basis indexed by Fin 2,
convert the two compressed bounded Hilbert operators to their
matrix representations, and apply MAN-61's Pauli matrix algebra.
The residual squares and anticommutator become scalar matrices.

The result is an exact parametrization of the residual spectral
degrees of freedom. Additional truth-algebra constraints are
required to decide six-dimensional Hamming metric realizability.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The two-dimensional residual subspace has a genuine
orthonormal basis indexed by Fin 2. -/
noncomputable def TwoDirectionExtremalSystem.sixDimResidualBasis
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6) :
    OrthonormalBasis (Fin 2) ℂ S.residual := by
  have hrank : Module.finrank ℂ S.residual = 2 :=
    twoDirection_sixDim_signedResidual_finrank
      S.uplus S.uminus S.vplus S.vminus hq hDim
  exact (stdOrthonormalBasis ℂ S.residual).reindex (finCongr hrank)

/-- The actual compressed A in its residual orthonormal basis. -/
noncomputable def TwoDirectionExtremalSystem.sixDimResidualMatrixA
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6) : TwoMat :=
  LinearMap.toMatrixOrthonormal (S.sixDimResidualBasis hq hDim)
    S.residualA.toLinearMap

/-- The actual compressed B in the same residual basis. -/
noncomputable def TwoDirectionExtremalSystem.sixDimResidualMatrixB
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6) : TwoMat :=
  LinearMap.toMatrixOrthonormal (S.sixDimResidualBasis hq hDim)
    S.residualB.toLinearMap

/-- The true residual coordinate A has a Hermitian matrix. -/
theorem TwoDirectionExtremalSystem.sixDimResidualMatrixA_isHermitian
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6) :
    (S.sixDimResidualMatrixA hq hDim).IsHermitian := by
  let b := S.sixDimResidualBasis hq hDim
  let a := S.residualA.toLinearMap
  have hself : IsSelfAdjoint S.residualA :=
    S.residualA_symmetric.isSelfAdjoint
  have hadj : a.adjoint = a :=
    (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff S.residualA).mpr hself
  change Matrix.conjTranspose (LinearMap.toMatrix b.toBasis b.toBasis a) =
    LinearMap.toMatrix b.toBasis b.toBasis a
  rw [← LinearMap.toMatrix_adjoint b b, hadj]

theorem TwoDirectionExtremalSystem.sixDimResidualMatrixB_isHermitian
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6) :
    (S.sixDimResidualMatrixB hq hDim).IsHermitian := by
  let b := S.sixDimResidualBasis hq hDim
  let a := S.residualB.toLinearMap
  have hself : IsSelfAdjoint S.residualB :=
    S.residualB_symmetric.isSelfAdjoint
  have hadj : a.adjoint = a :=
    (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff S.residualB).mpr hself
  change Matrix.conjTranspose (LinearMap.toMatrix b.toBasis b.toBasis a) =
    LinearMap.toMatrix b.toBasis b.toBasis a
  rw [← LinearMap.toMatrix_adjoint b b, hadj]

/-- Ambient trace zero implies the six-dimensional residual A
is a trace-zero 2x2 Hermitian matrix. -/
theorem TwoDirectionExtremalSystem.sixDimResidualMatrixA_trace_zero
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htr : LinearMap.trace ℂ E S.A.toLinearMap = 0) :
    (S.sixDimResidualMatrixA hq hDim).trace = 0 := by
  calc
    (S.sixDimResidualMatrixA hq hDim).trace =
        LinearMap.trace ℂ S.residual S.residualA.toLinearMap := by
      exact (LinearMap.trace_eq_matrix_trace ℂ
        (S.sixDimResidualBasis hq hDim).toBasis
        S.residualA.toLinearMap).symm
    _ = 0 := S.residualA_trace_zero hq htr

theorem TwoDirectionExtremalSystem.sixDimResidualMatrixB_trace_zero
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htr : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    (S.sixDimResidualMatrixB hq hDim).trace = 0 := by
  calc
    (S.sixDimResidualMatrixB hq hDim).trace =
        LinearMap.trace ℂ S.residual S.residualB.toLinearMap := by
      exact (LinearMap.trace_eq_matrix_trace ℂ
        (S.sixDimResidualBasis hq hDim).toBasis
        S.residualB.toLinearMap).symm
    _ = 0 := S.residualB_trace_zero hq htr

/-- The two actual residual coordinate matrices admit their
full complex Pauli normal forms in the same Hilbert basis. -/
theorem TwoDirectionExtremalSystem.sixDimResidualMatrices_pauli
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    let MA := S.sixDimResidualMatrixA hq hDim
    let MB := S.sixDimResidualMatrixB hq hDim
    MA = pauliResidualMatrix (MA 0 0) (MA 0 1) ∧
    MB = pauliResidualMatrix (MB 0 0) (MB 0 1) := by
  dsimp
  exact ⟨twoDim_tracelessHermitian_pauli_normal_form
    _ (S.sixDimResidualMatrixA_isHermitian hq hDim)
      (S.sixDimResidualMatrixA_trace_zero hq hDim htrA),
    twoDim_tracelessHermitian_pauli_normal_form
    _ (S.sixDimResidualMatrixB_isHermitian hq hDim)
      (S.sixDimResidualMatrixB_trace_zero hq hDim htrB)⟩

/-- The anticommutator of the actual two residual coordinate matrices
is a scalar multiple of the 2x2 identity. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_anticommutator_scalar
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    let MA := S.sixDimResidualMatrixA hq hDim
    let MB := S.sixDimResidualMatrixB hq hDim
    MA * MB + MB * MA =
      Matrix.diagonal (fun _ : Fin 2 =>
        2 * (MA 0 0) * (MB 0 0) +
          (MA 0 1) * star (MB 0 1) +
          (MB 0 1) * star (MA 0 1)) := by
  dsimp
  exact twoDim_tracelessHermitian_anticommutator_scalar _ _
    (S.sixDimResidualMatrixA_isHermitian hq hDim)
    (S.sixDimResidualMatrixB_isHermitian hq hDim)
    (S.sixDimResidualMatrixA_trace_zero hq hDim htrA)
    (S.sixDimResidualMatrixB_trace_zero hq hDim htrB)

end Neoplatonic.LTR
