import Neoplatonic.LTR.SixDimensionalRealPauliGram
import Mathlib.Tactic

/-!
# LTR-MAN-72: genuine real Pauli vector and Gram matrix

A traceless Hermitian 2×2 matrix
  [[a, z], [star z, -a]]
has a canonical real coordinate triple (Re a, Re z, Im z).
MAN-65 provides precisely these matrices for the actual 6D residual.

We identify the complex scalar square and anticommutator coefficients
with the Euclidean Gram data of these triples. The Lagrange identity
then proves positive semidefiniteness of the Gram matrix and MAN-71/72
supply the simultaneous contraction budget.

The Pauli-vector sign convention on the third coordinate is irrelevant
for lengths and pairwise Gram products, because the same basis is used
for both matrices.
-/

namespace Neoplatonic.LTR

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- Real Pauli coordinate triple for a complex 2×2 matrix. -/
noncomputable def pauliRealVector (M : TwoMat) : Fin 3 → ℝ :=
  ![(M 0 0).re, (M 0 1).re, (M 0 1).im]

/-- The ordinary Euclidean dot product of the Pauli triples. -/
noncomputable def pauliRealDot (M N : TwoMat) : ℝ :=
  ∑ i : Fin 3, pauliRealVector M i * pauliRealVector N i

theorem pauliRealDot_coordinates (M N : TwoMat) :
    pauliRealDot M N =
      (M 0 0).re * (N 0 0).re +
      (M 0 1).re * (N 0 1).re +
      (M 0 1).im * (N 0 1).im := by
  simp [pauliRealDot, pauliRealVector, Fin.sum_univ_three]

/-- Hermitianity makes the upper-left diagonal Pauli parameter real. -/
theorem pauliRealVector_diagonal_im_zero
    (M : TwoMat) (hM : M.IsHermitian) :
    (M 0 0).im = 0 := by
  have hself : IsSelfAdjoint (M 0 0) := hM.apply 0 0
  exact (Complex.im_eq_zero_iff_isSelfAdjoint _).2 hself

/-- The quadratic Pauli coefficient is the dot square of the
canonical real three-vector. -/
theorem pauliRealQuadratic_eq_dot
    (M : TwoMat) (hM : M.IsHermitian) :
    pauliRealQuadratic M = pauliRealDot M M := by
  have ha := pauliRealVector_diagonal_im_zero M hM
  rw [pauliRealDot_coordinates]
  simp [pauliRealQuadratic, pauliQuadratic, Complex.mul_re,
    Complex.star_def, ha, pow_two]
  <;> ring

/-- The real scalar anticommutator coefficient is twice the
Euclidean inner product. -/
theorem pauliRealMixed_eq_two_dot
    (M N : TwoMat) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    pauliRealMixed M N = 2 * pauliRealDot M N := by
  have ha := pauliRealVector_diagonal_im_zero M hM
  have hb := pauliRealVector_diagonal_im_zero N hN
  rw [pauliRealDot_coordinates]
  simp [pauliRealMixed, pauliMixed, Complex.mul_re,
    Complex.star_def, ha, hb]
  <;> ring

/-- The dot square of any real Pauli triple is nonnegative. -/
theorem pauliRealDot_self_nonneg (M : TwoMat) :
    0 ≤ pauliRealDot M M := by
  rw [pauliRealDot_coordinates]
  nlinarith only [sq_nonneg (M 0 0).re,
    sq_nonneg (M 0 1).re, sq_nonneg (M 0 1).im]

/-- Lagrange's identity for the two real Pauli vectors, expressed
through their three 2×2 minors. -/
theorem pauliRealDot_lagrange (M N : TwoMat) :
    pauliRealDot M M * pauliRealDot N N -
      (pauliRealDot M N) ^ 2 =
      ((M 0 0).re * (N 0 1).re -
        (M 0 1).re * (N 0 0).re) ^ 2 +
      ((M 0 0).re * (N 0 1).im -
        (M 0 1).im * (N 0 0).re) ^ 2 +
      ((M 0 1).re * (N 0 1).im -
        (M 0 1).im * (N 0 1).re) ^ 2 := by
  simp only [pauliRealDot_coordinates]
  ring

/-- Positive semidefiniteness of the real Pauli Gram matrix. -/
theorem pauliRealDot_cauchy (M N : TwoMat) :
    (pauliRealDot M N) ^ 2 ≤
      pauliRealDot M M * pauliRealDot N N := by
  have h := pauliRealDot_lagrange M N
  have hpos : 0 ≤
      ((M 0 0).re * (N 0 1).re -
        (M 0 1).re * (N 0 0).re) ^ 2 +
      ((M 0 0).re * (N 0 1).im -
        (M 0 1).im * (N 0 0).re) ^ 2 +
      ((M 0 1).re * (N 0 1).im -
        (M 0 1).im * (N 0 1).re) ^ 2 := by
    positivity
  linarith

/-- Hermitian Pauli matrices have nonnegative real quadratic
coefficients. -/
theorem pauliRealQuadratic_nonneg (M : TwoMat) (hM : M.IsHermitian) :
    0 ≤ pauliRealQuadratic M := by
  rw [pauliRealQuadratic_eq_dot M hM]
  exact pauliRealDot_self_nonneg M

/-- The mixed coefficient and two squared lengths satisfy the
2×2 principal-minor inequality of a positive semidefinite Gram
matrix. -/
theorem twoDim_pauli_realGram_psd
    (M N : TwoMat) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    (pauliRealMixed M N) ^ 2 ≤
      4 * pauliRealQuadratic M * pauliRealQuadratic N := by
  rw [pauliRealMixed_eq_two_dot M N hM hN,
    pauliRealQuadratic_eq_dot M hM,
    pauliRealQuadratic_eq_dot N hN]
  have h := pauliRealDot_cauchy M N
  nlinarith

section SixDimensionalActualResidual

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Complete real Gram-cone constraints for the two genuine
compressed six-dimensional Hamming-coordinate operators. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_realGram_cone
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    let M := S.sixDimResidualMatrixA hq hDim
    let N := S.sixDimResidualMatrixB hq hDim
    0 ≤ pauliRealQuadratic M ∧
    0 ≤ pauliRealQuadratic N ∧
    (pauliRealMixed M N) ^ 2 ≤
      4 * pauliRealQuadratic M * pauliRealQuadratic N ∧
    pauliRealQuadratic M + pauliRealQuadratic N +
      |pauliRealMixed M N| ≤ 1 := by
  dsimp only
  have hM := S.sixDimResidualMatrixA_isHermitian hq hDim
  have hN := S.sixDimResidualMatrixB_isHermitian hq hDim
  exact ⟨pauliRealQuadratic_nonneg _ hM,
    pauliRealQuadratic_nonneg _ hN,
    twoDim_pauli_realGram_psd _ _ hM hN,
    S.sixDimResidual_realGram_bound hq hDim htrA htrB⟩

/-- The same actual contraction budget in Euclidean Pauli triples. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_realVectorGram_bound
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    let M := S.sixDimResidualMatrixA hq hDim
    let N := S.sixDimResidualMatrixB hq hDim
    pauliRealDot M M + pauliRealDot N N +
      2 * |pauliRealDot M N| ≤ 1 := by
  have h := S.sixDimResidual_realGram_bound hq hDim htrA htrB
  change pauliRealQuadratic (S.sixDimResidualMatrixA hq hDim) +
    pauliRealQuadratic (S.sixDimResidualMatrixB hq hDim) +
    |pauliRealMixed (S.sixDimResidualMatrixA hq hDim)
      (S.sixDimResidualMatrixB hq hDim)| ≤ 1 at h
  rw [pauliRealQuadratic_eq_dot _
      (S.sixDimResidualMatrixA_isHermitian hq hDim),
    pauliRealQuadratic_eq_dot _
      (S.sixDimResidualMatrixB_isHermitian hq hDim),
    pauliRealMixed_eq_two_dot _ _
      (S.sixDimResidualMatrixA_isHermitian hq hDim)
      (S.sixDimResidualMatrixB_isHermitian hq hDim)] at h
  simpa [abs_mul] using h

end SixDimensionalActualResidual

end Neoplatonic.LTR
