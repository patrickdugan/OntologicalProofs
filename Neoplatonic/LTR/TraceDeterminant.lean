import Mathlib

/-!
# Trace series and the logarithmic derivative of a determinant

For an arbitrary finite real matrix, the reciprocal determinant has logarithmic
derivative `trace ((1 - z • A)⁻¹ * A)` wherever its denominator is nonzero.
When `‖z • A‖ < 1` in the infinity operator norm, this quantity is the sum of
the convergent series `∑ k, z ^ k * trace (A ^ (k + 1))`.

The real logarithm below is Mathlib's `Real.log`, hence equals the logarithm of
the absolute value on nonzero inputs. This file proves the differential
trace–determinant identity. Integrating it to the exponential formula with
coefficients `trace (A ^ k) / k` is a separate step.
-/

namespace Neoplatonic.LTR.TraceDeterminant

open Matrix Polynomial
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Evaluating the determinant polynomial commutes with scalar evaluation. -/
theorem det_one_add_polynomial_eval (B : Matrix n n ℝ) (t : ℝ) :
    (det (1 + (X : ℝ[X]) • B.map C)).eval t = (1 + t • B).det := by
  change (Polynomial.evalRingHom t) _ = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    Matrix.one_apply, apply_ite]

/-- The derivative of an affine determinant at the identity is the trace. -/
theorem hasDerivAt_det_one_add (B : Matrix n n ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • B).det) B.trace 0 := by
  have h := (det (1 + (X : ℝ[X]) • B.map C)).hasDerivAt (0 : ℝ)
  rw [Matrix.derivative_det_one_add_X_smul] at h
  simpa only [det_one_add_polynomial_eval] using h

/-- Factoring an affine matrix curve through its invertible base point. -/
theorem det_affine_factor (M B : Matrix n n ℝ) (hM : M.det ≠ 0) (t : ℝ) :
    (M + t • B).det = M.det * (1 + t • (M⁻¹ * B)).det := by
  rw [← Matrix.det_mul]
  congr 1
  rw [mul_add, mul_one, mul_smul_comm,
    Matrix.mul_nonsing_inv_cancel_left M B (isUnit_iff_ne_zero.mpr hM)]

/-- Jacobi's formula for an arbitrary affine matrix curve at a nonsingular point. -/
theorem hasDerivAt_det_affine (M B : Matrix n n ℝ) (hM : M.det ≠ 0) :
    HasDerivAt (fun t : ℝ => (M + t • B).det)
      (M.det * (M⁻¹ * B).trace) 0 := by
  convert (hasDerivAt_det_one_add (M⁻¹ * B)).const_mul M.det using 1
  ext t
  exact det_affine_factor M B hM t

/-- The denominator of the finite matrix zeta function. -/
noncomputable def denominator (A : Matrix n n ℝ) (z : ℝ) : ℝ :=
  (1 - z • A).det

/-- The reciprocal determinant, defined as a real function. -/
noncomputable def zeta (A : Matrix n n ℝ) (z : ℝ) : ℝ :=
  (denominator A z)⁻¹

theorem denominator_zero (A : Matrix n n ℝ) : denominator A 0 = 1 := by
  simp [denominator]

theorem zeta_zero (A : Matrix n n ℝ) : zeta A 0 = 1 := by
  simp [zeta, denominator_zero]

/-- Jacobi's formula at an arbitrary parameter with a nonsingular denominator. -/
theorem hasDerivAt_denominator (A : Matrix n n ℝ) (z : ℝ)
    (hz : denominator A z ≠ 0) :
    HasDerivAt (denominator A)
      (-(denominator A z) * ((1 - z • A)⁻¹ * A).trace) z := by
  have hbase := hasDerivAt_det_affine (1 - z • A) (-A) hz
  have hinner : HasDerivAt (fun t : ℝ => t - z) 1 z := by
    simpa using (hasDerivAt_id z).sub_const z
  have houter : HasDerivAt (fun t : ℝ => (1 - z • A + t • (-A)).det)
      ((1 - z • A).det * ((1 - z • A)⁻¹ * (-A)).trace) (z - z) := by
    simpa using hbase
  have h := houter.comp z hinner
  have heq : (fun t : ℝ => (1 - z • A + (t - z) • (-A)).det) =
      denominator A := by
    funext t
    dsimp [denominator]
    congr 1
    simp only [sub_smul, smul_neg]
    abel
  rw [heq] at h
  simpa only [mul_one, mul_neg, Matrix.trace_neg, neg_mul, denominator] using h

/-- The logarithmic derivative formula uses `Real.log`, which takes the absolute
value of a nonzero negative argument. -/
theorem hasDerivAt_neg_log_denominator (A : Matrix n n ℝ) (z : ℝ)
    (hz : denominator A z ≠ 0) :
    HasDerivAt (fun t : ℝ => -Real.log (denominator A t))
      ((1 - z • A)⁻¹ * A).trace z := by
  convert ((hasDerivAt_denominator A z hz).log hz).neg using 1
  field_simp [hz]
  <;> ring

/-- The reciprocal determinant solves a scalar differential equation. -/
theorem hasDerivAt_zeta (A : Matrix n n ℝ) (z : ℝ)
    (hz : denominator A z ≠ 0) :
    HasDerivAt (zeta A)
      (zeta A z * ((1 - z • A)⁻¹ * A).trace) z := by
  convert (hasDerivAt_denominator A z hz).inv hz using 1
  <;> dsimp [zeta]
  <;> field_simp [hz]
  <;> ring

/-- The norm condition supplies the nonsingularity needed by Jacobi's formula. -/
theorem denominator_ne_zero_of_norm_lt_one (A : Matrix n n ℝ) (z : ℝ)
    (hz : ‖z • A‖ < 1) : denominator A z ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_of_norm_lt_one hz)

/-- The full trace series converges to the trace of the resolvent times `A`. -/
theorem trace_resolvent_hasSum (A : Matrix n n ℝ) (z : ℝ)
    (hz : ‖z • A‖ < 1) :
    HasSum (fun k : ℕ => z ^ k * (A ^ (k + 1)).trace)
      ((1 - z • A)⁻¹ * A).trace := by
  have hg : HasSum (fun k : ℕ => (z • A) ^ k) (1 - z • A)⁻¹ := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using
      hasSum_geom_series_inverse (z • A) hz
  have ht := (hg.mul_right A).map (Matrix.traceAddMonoidHom n ℝ)
    continuous_id.matrix_trace
  simpa only [smul_pow, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, pow_succ] using ht

/-- Differential form of the general finite-dimensional trace–determinant zeta
identity, with convergence certified by an explicit norm condition. -/
theorem trace_series_log_derivative (A : Matrix n n ℝ) (z : ℝ)
    (hz : ‖z • A‖ < 1) :
    HasSum (fun k : ℕ => z ^ k * (A ^ (k + 1)).trace)
      (deriv (fun t : ℝ => -Real.log (denominator A t)) z) := by
  rw [(hasDerivAt_neg_log_denominator A z
    (denominator_ne_zero_of_norm_lt_one A z hz)).deriv]
  exact trace_resolvent_hasSum A z hz

/-- The scalar zeta equation expressed through all positive trace moments. -/
theorem zeta_derivative_eq_trace_series (A : Matrix n n ℝ) (z : ℝ)
    (hz : ‖z • A‖ < 1) :
    deriv (zeta A) z =
      zeta A z * ∑' k : ℕ, z ^ k * (A ^ (k + 1)).trace := by
  rw [(hasDerivAt_zeta A z (denominator_ne_zero_of_norm_lt_one A z hz)).deriv,
    (trace_resolvent_hasSum A z hz).tsum_eq]

end Neoplatonic.LTR.TraceDeterminant
