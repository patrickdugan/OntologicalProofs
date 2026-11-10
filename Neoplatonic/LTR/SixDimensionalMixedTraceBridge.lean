import Neoplatonic.LTR.SixDimensionalLabelledCommutators
import Neoplatonic.LTR.TwoDimensionalRealPauliVectors
import Neoplatonic.LTR.SixDimensionalTruePauliBounds
import Neoplatonic.LTR.EigenquartetTrace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-75: the Pauli mixed coefficient is the ambient trace of AB

The four signed extremal eigenvectors of a two-direction Hamming
contraction are killed by the *other* coordinate operator. Their
span therefore contributes zero to the trace of A*B. MAN-62's
orthogonal trace decomposition leaves only the invariant residual
operator product.

In dimension six the residual has a common two-dimensional
orthonormal basis. MAN-65/68/69/70 identify its matrices with
C*-isometric Euclidean conjugates, and these identifications
also preserve products and traces. For traceless Hermitian 2×2
residual matrices, trace(M*N) is exactly their mixed Pauli
coefficient (the real quantity 2 m · n of MAN-72).

The resulting equation is

    trace(A*B) = pauliMixed M N,

for any actual six-dimensional TwoDirectionExtremalSystem with the
signed orthonormal quartet and ambient coordinate trace zero.

It remains to instantiate a concrete labelled Dirac system from
MAN-74 in the extremal-system structure and to combine its
opposite-corner support trace theorem with this identity.
-/

namespace Neoplatonic.LTR

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ
private abbrev TwoEuclidean := EuclideanSpace ℂ (Fin 2)

/-- For any two traceless Hermitian Pauli matrices, the trace
of their ordered product is the scalar anticommutator coefficient. -/
theorem twoDim_pauli_mixed_eq_product_trace
    (M N : TwoMat) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0) :
    (M * N).trace = pauliMixed M N := by
  rw [twoDim_tracelessHermitian_pauli_normal_form M hM htrM,
    twoDim_tracelessHermitian_pauli_normal_form N hN htrN]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two, pauliResidualMatrix, pauliMixed] <;> ring

/-- Conjugation by a common linear isometry preserves composition
of bounded complex Hilbert operators. -/
theorem hilbertIsometricConjugate_mul
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (A B : E →L[ℂ] E) :
    hilbertIsometricConjugate U (A * B) =
      hilbertIsometricConjugate U A *
        hilbertIsometricConjugate U B := by
  ext x
  change U (A (B (U.symm x))) =
    U (A (U.symm (U (B (U.symm x)))))
  simp

/-- Isometric conjugation of a bounded operator preserves its
finite-dimensional complex-linear endomorphism trace. -/
theorem hilbertIsometricConjugate_trace
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    LinearMap.trace ℂ F (hilbertIsometricConjugate U T).toLinearMap =
      LinearMap.trace ℂ E T.toLinearMap := by
  have hmap : (hilbertIsometricConjugate U T).toLinearMap =
      U.toLinearEquiv.conj T.toLinearMap := by
    ext x
    rfl
  rw [hmap]
  exact LinearMap.trace_conj' T.toLinearMap U.toLinearEquiv

/-- The inverse of Mathlib's matrix-to-Euclidean bounded operator
star algebra equivalence is multiplicative. -/
theorem twoEuclideanCstarMatrix_mul
    (T U : TwoEuclidean →L[ℂ] TwoEuclidean) :
    twoEuclideanCstarMatrix (T * U) =
      twoEuclideanCstarMatrix T * twoEuclideanCstarMatrix U := by
  unfold twoEuclideanCstarMatrix
  exact map_mul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm T U

section ActualSixDimensionalResidual

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The four signed extremal directions contribute no mixed
trace: the ambient trace of A*B equals the trace of the true
compressed residual product in every finite dimension. -/
theorem TwoDirectionExtremalSystem.ambientProduct_trace_eq_residual
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus)) :
    LinearMap.trace ℂ E (S.A.toLinearMap * S.B.toLinearMap) =
      LinearMap.trace ℂ S.residual
        (S.residualA.toLinearMap * S.residualB.toLinearMap) := by
  let q := twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  let K := Submodule.span ℂ (Set.range q)
  let T := S.A.toLinearMap * S.B.toLinearMap
  have hEig : ∀ i : Fin 4, T (q i) = (0 : ℂ) • q i := by
    intro i
    simp only [zero_smul]
    have ha := S.eigenquartet_A i
    have hb := S.eigenquartet_B i
    change S.A.toLinearMap (S.B.toLinearMap (q i)) = 0
    rw [hb, map_smul, ha]
    fin_cases i <;>
      simp [twoDirectionAQuartetEigenvalues,
        twoDirectionBQuartetEigenvalues]
  have hK := eigenquartet_span_invariant q T (fun _ => 0) hEig
  have hR : ∀ x ∈ Kᗮ, T x ∈ Kᗮ := by
    intro x hx
    change x ∈ S.residual at hx
    have hb := (S.residual_invariant x hx).2
    have ha := (S.residual_invariant (S.B x) hb).1
    change S.A (S.B x) ∈ S.residual
    exact ha
  have hsplit := orthogonalTwoSummands_trace K T hK hR
  have hquartet := eigenquartet_span_restrict_trace
    q hq T (fun _ => 0) hEig hK
  have hzero : LinearMap.trace ℂ K (T.restrict hK) = 0 := by
    simpa using hquartet
  rw [hzero, zero_add] at hsplit
  have hres :
      T.restrict hR =
        S.residualA.toLinearMap * S.residualB.toLinearMap := by
    ext x
    rfl
  rw [hres] at hsplit
  exact hsplit

/-- The matrix of the actual residual operator product in the
common MAN-65 orthonormal basis has exactly the residual operator
trace. This uses the genuine two-dimensional C*-matrix map. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_product_matrixTrace
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6) :
    (S.sixDimResidualMatrixA hq hDim *
      S.sixDimResidualMatrixB hq hDim).trace =
        LinearMap.trace ℂ S.residual
          (S.residualA.toLinearMap * S.residualB.toLinearMap) := by
  let U := (S.sixDimResidualBasis hq hDim).repr
  have htr := twoEuclideanCstarMatrix_trace
    (S.sixDimEuclideanResidualA hq hDim *
      S.sixDimEuclideanResidualB hq hDim)
  rw [twoEuclideanCstarMatrix_mul] at htr
  change (S.sixDimCstarResidualMatrixA hq hDim *
    S.sixDimCstarResidualMatrixB hq hDim).trace = _ at htr
  rw [S.sixDimCstarResidualMatrixA_eq hq hDim,
    S.sixDimCstarResidualMatrixB_eq hq hDim] at htr
  have hmul :
      S.sixDimEuclideanResidualA hq hDim *
        S.sixDimEuclideanResidualB hq hDim =
      hilbertIsometricConjugate U (S.residualA * S.residualB) := by
    exact (hilbertIsometricConjugate_mul
      U S.residualA S.residualB).symm
  rw [hmul] at htr
  rw [hilbertIsometricConjugate_trace] at htr
  exact htr

/-- Concrete ambient mixed trace is exactly the Pauli Gram
mixed coefficient of the actual two-dimensional residual, without
any assumption that the ordered operator products vanish. -/
theorem TwoDirectionExtremalSystem.sixDim_ambientProduct_trace_eq_pauliMixed
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    LinearMap.trace ℂ E (S.A.toLinearMap * S.B.toLinearMap) =
      pauliMixed (S.sixDimResidualMatrixA hq hDim)
        (S.sixDimResidualMatrixB hq hDim) := by
  calc
    LinearMap.trace ℂ E (S.A.toLinearMap * S.B.toLinearMap) =
        LinearMap.trace ℂ S.residual
          (S.residualA.toLinearMap * S.residualB.toLinearMap) :=
      S.ambientProduct_trace_eq_residual hq
    _ = (S.sixDimResidualMatrixA hq hDim *
          S.sixDimResidualMatrixB hq hDim).trace :=
      (S.sixDimResidual_product_matrixTrace hq hDim).symm
    _ = pauliMixed (S.sixDimResidualMatrixA hq hDim)
          (S.sixDimResidualMatrixB hq hDim) :=
      twoDim_pauli_mixed_eq_product_trace _ _
        (S.sixDimResidualMatrixA_isHermitian hq hDim)
        (S.sixDimResidualMatrixB_isHermitian hq hDim)
        (S.sixDimResidualMatrixA_trace_zero hq hDim htrA)
        (S.sixDimResidualMatrixB_trace_zero hq hDim htrB)

end ActualSixDimensionalResidual
end Neoplatonic.LTR
