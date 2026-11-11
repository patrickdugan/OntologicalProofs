import Neoplatonic.LTR.SixDimensionalSaturatedRankOneBlocks
import Mathlib.Tactic

/-!
# LTR-MAN-87: half-saturated residual Pauli matrices coincide up to sign

MAN-85 proves that saturation of the signed eigenquartet's residual
Pauli mixed Gram coefficient forces both real squared Pauli lengths
to 1/4 and the absolute mixed coefficient to 1/2.

Over real three-dimensional Pauli coordinates this equality makes
either the sum or the difference of the two vectors have zero
squared length. All three components therefore coincide, or are
each other's negatives.

MAN-61's exact traceless-Hermitian 2x2 Pauli normal form converts
that vector rigidity into actual MATRIX equality M = N or M = -N
in the same two-dimensional residual orthonormal Hilbert basis.

Thus one of the signed Hamming witness combinations M-N and M+N
vanishes identically on the entire residual subspace.
-/

namespace Neoplatonic.LTR

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- Two saturated real Pauli Gram vectors have identical or
opposite coordinates, with every real component certified. -/
theorem pauliRealVectors_halfSat_equal_or_opposite
    (M N : TwoMat) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (hq : pauliRealQuadratic M = (1 / 4 : ℝ))
    (hr : pauliRealQuadratic N = (1 / 4 : ℝ))
    (hc : |pauliRealMixed M N| = (1 / 2 : ℝ)) :
    (∀ i : Fin 3, pauliRealVector M i = pauliRealVector N i) ∨
    (∀ i : Fin 3, pauliRealVector M i = -pauliRealVector N i) := by
  let a : ℝ := (M 0 0).re
  let b : ℝ := (M 0 1).re
  let c : ℝ := (M 0 1).im
  let d : ℝ := (N 0 0).re
  let e : ℝ := (N 0 1).re
  let f : ℝ := (N 0 1).im
  rw [pauliRealQuadratic_eq_dot M hM, pauliRealDot_coordinates] at hq
  rw [pauliRealQuadratic_eq_dot N hN, pauliRealDot_coordinates] at hr
  rw [pauliRealMixed_eq_two_dot M N hM hN,
    pauliRealDot_coordinates] at hc
  have hqm : a * a + b * b + c * c = (1 / 4 : ℝ) := hq
  have hrn : d * d + e * e + f * f = (1 / 4 : ℝ) := hr
  have hmix : |2 * (a * d + b * e + c * f)| = (1 / 2 : ℝ) := hc
  by_cases hs : 0 ≤ 2 * (a * d + b * e + c * f)
  · have hdot : 2 * (a * d + b * e + c * f) = (1 / 2 : ℝ) := by
      simpa only [abs_of_nonneg hs] using hmix
    have hzero : (a - d) ^ 2 + (b - e) ^ 2 + (c - f) ^ 2 = 0 := by
      nlinarith [hqm, hrn, hdot]
    have ha : a = d := by
      nlinarith [sq_nonneg (b - e), sq_nonneg (c - f)]
    have hb : b = e := by
      nlinarith [sq_nonneg (a - d), sq_nonneg (c - f)]
    have hc' : c = f := by
      nlinarith [sq_nonneg (a - d), sq_nonneg (b - e)]
    left
    intro i
    fin_cases i
    · simpa [pauliRealVector, a, d] using ha
    · simpa [pauliRealVector, b, e] using hb
    · simpa [pauliRealVector, c, f] using hc'
  · have hsneg : 2 * (a * d + b * e + c * f) ≤ 0 :=
      le_of_lt (lt_of_not_ge hs)
    have hdot : 2 * (a * d + b * e + c * f) = -(1 / 2 : ℝ) := by
      rw [abs_of_nonpos hsneg] at hmix
      linarith
    have hzero : (a + d) ^ 2 + (b + e) ^ 2 + (c + f) ^ 2 = 0 := by
      nlinarith [hqm, hrn, hdot]
    have ha : a = -d := by
      nlinarith [sq_nonneg (b + e), sq_nonneg (c + f)]
    have hb : b = -e := by
      nlinarith [sq_nonneg (a + d), sq_nonneg (c + f)]
    have hc' : c = -f := by
      nlinarith [sq_nonneg (a + d), sq_nonneg (b + e)]
    right
    intro i
    fin_cases i
    · simpa [pauliRealVector, a, d] using ha
    · simpa [pauliRealVector, b, e] using hb
    · simpa [pauliRealVector, c, f] using hc'

/-- For traceless Hermitian 2x2 matrices, equality of the three
real Pauli coordinates implies actual matrix equality. -/
theorem twoDim_pauliRealVector_equal_implies_matrix_equal
    (M N : TwoMat) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0)
    (hvec : ∀ i : Fin 3,
      pauliRealVector M i = pauliRealVector N i) :
    M = N := by
  have haRe : (M 0 0).re = (N 0 0).re := by
    simpa [pauliRealVector] using hvec 0
  have hzRe : (M 0 1).re = (N 0 1).re := by
    simpa [pauliRealVector] using hvec 1
  have hzIm : (M 0 1).im = (N 0 1).im := by
    simpa [pauliRealVector] using hvec 2
  have ha : M 0 0 = N 0 0 := by
    apply Complex.ext
    · exact haRe
    · rw [pauliRealVector_diagonal_im_zero M hM,
        pauliRealVector_diagonal_im_zero N hN]
  have hz : M 0 1 = N 0 1 := Complex.ext hzRe hzIm
  calc
    M = pauliResidualMatrix (M 0 0) (M 0 1) :=
      twoDim_tracelessHermitian_pauli_normal_form M hM htrM
    _ = pauliResidualMatrix (N 0 0) (N 0 1) := by rw [ha, hz]
    _ = N := (twoDim_tracelessHermitian_pauli_normal_form N hN htrN).symm

/-- Opposite Pauli-coordinate triples imply exactly negated
traceless Hermitian matrices in the same residual basis. -/
theorem twoDim_pauliRealVector_opposite_implies_matrix_negative
    (M N : TwoMat) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0)
    (hvec : ∀ i : Fin 3,
      pauliRealVector M i = -pauliRealVector N i) :
    M = -N := by
  have haRe : (M 0 0).re = -(N 0 0).re := by
    simpa [pauliRealVector] using hvec 0
  have hzRe : (M 0 1).re = -(N 0 1).re := by
    simpa [pauliRealVector] using hvec 1
  have hzIm : (M 0 1).im = -(N 0 1).im := by
    simpa [pauliRealVector] using hvec 2
  have ha : M 0 0 = -(N 0 0) := by
    apply Complex.ext
    · simpa using haRe
    · simp [pauliRealVector_diagonal_im_zero M hM,
        pauliRealVector_diagonal_im_zero N hN]
  have hz : M 0 1 = -(N 0 1) := by
    apply Complex.ext
    · simpa using hzRe
    · simpa using hzIm
  calc
    M = pauliResidualMatrix (M 0 0) (M 0 1) :=
      twoDim_tracelessHermitian_pauli_normal_form M hM htrM
    _ = -(pauliResidualMatrix (N 0 0) (N 0 1)) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pauliResidualMatrix, ha, hz, Matrix.neg_apply]
    _ = -N := by
      exact congrArg (fun X : TwoMat => -X)
        (twoDim_tracelessHermitian_pauli_normal_form N hN htrN).symm

/-- Sharp half-saturation of the real mixed Gram coefficient
forces actual matrix coincidence up to sign. -/
theorem twoDim_pauli_halfSat_matrices_equal_or_negative
    (M N : TwoMat) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0)
    (hq : pauliRealQuadratic M = (1 / 4 : ℝ))
    (hr : pauliRealQuadratic N = (1 / 4 : ℝ))
    (hc : |pauliRealMixed M N| = (1 / 2 : ℝ)) :
    M = N ∨ M = -N := by
  rcases pauliRealVectors_halfSat_equal_or_opposite
    M N hM hN hq hr hc with hv | hv
  · exact Or.inl (twoDim_pauliRealVector_equal_implies_matrix_equal
      M N hM hN htrM htrN hv)
  · exact Or.inr (twoDim_pauliRealVector_opposite_implies_matrix_negative
      M N hM hN htrM htrN hv)

/-- The two genuine residual coordinate matrices from a 6D signed
eigenquartet coincide up to sign at maximal Pauli mixed overlap.
One signed Hamming witness therefore acts as zero on the residual. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_halfSat_matrixEqualOrNeg
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0)
    (hsat : |pauliRealMixed
        (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp))| = (1 / 2 : ℝ)) :
    S.sixDimResidualMatrixA hq (by simp) =
      S.sixDimResidualMatrixB hq (by simp) ∨
    S.sixDimResidualMatrixA hq (by simp) =
      -(S.sixDimResidualMatrixB hq (by simp)) := by
  obtain ⟨hqval, hrval, _⟩ :=
    S.sixDimResidual_half_saturation_rigid hq htrA htrB hsat
  exact twoDim_pauli_halfSat_matrices_equal_or_negative
    _ _
    (S.sixDimResidualMatrixA_isHermitian hq (by simp))
    (S.sixDimResidualMatrixB_isHermitian hq (by simp))
    (S.sixDimResidualMatrixA_trace_zero hq (by simp) htrA)
    (S.sixDimResidualMatrixB_trace_zero hq (by simp) htrB)
    hqval hrval hsat

end Neoplatonic.LTR
