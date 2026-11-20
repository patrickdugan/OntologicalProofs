import Mathlib

/-!
# Trace series and the logarithmic derivative of a determinant

For an arbitrary finite real matrix, the reciprocal determinant has logarithmic
derivative `trace ((1 - z • A)⁻¹ * A)` wherever its denominator is nonzero.
When `‖z • A‖ < 1` in the infinity operator norm, this quantity is the sum of
the convergent series `∑ k, z ^ k * trace (A ^ (k + 1))`.

The trace logarithm series is summable under the same norm bound, and its
exponential equals the reciprocal determinant. The proof differentiates the
series on a certified interval and fixes the integration constant at zero.
The intermediate real logarithm uses Mathlib's `Real.log` on nonzero inputs.
-/

namespace Neoplatonic.LTR.TraceDeterminant

open Matrix Polynomial
open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

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
  <;> ring

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
  have h := houter.comp (h := fun t : ℝ => t - z) z hinner
  simp only [Function.comp_def, mul_one] at h
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
  · funext t
    rfl
  · change (denominator A z)⁻¹ * ((1 - z • A)⁻¹ * A).trace =
      -(-denominator A z * ((1 - z • A)⁻¹ * A).trace) / denominator A z ^ 2
    field_simp [hz]
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
  change HasSum (fun k : ℕ => ((z • A) ^ k * A).trace)
    ((1 - z • A)⁻¹ * A).trace at ht
  simpa only [_root_.smul_pow, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, pow_succ]
    using ht

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

/-- The trace as a continuous linear map for the infinity operator norm. -/
noncomputable def traceCLM : Matrix n n ℝ →L[ℝ] ℝ where
  toLinearMap := Matrix.traceLinearMap n ℝ ℝ
  cont := continuous_id.matrix_trace

theorem trace_norm_bound (M : Matrix n n ℝ) :
    ‖M.trace‖ ≤ ‖traceCLM (n := n)‖ * ‖M‖ :=
  (traceCLM (n := n)).le_opNorm M

/-- One term of the trace logarithm, indexed by positive powers. -/
noncomputable def logTraceTerm (A : Matrix n n ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  z ^ (k + 1) * (A ^ (k + 1)).trace / (k + 1 : ℝ)

/-- The convergent trace logarithm near the origin. -/
noncomputable def logTrace (A : Matrix n n ℝ) (z : ℝ) : ℝ :=
  ∑' k : ℕ, logTraceTerm A k z

theorem logTrace_zero (A : Matrix n n ℝ) : logTrace A 0 = 0 := by
  simp [logTrace, logTraceTerm]

theorem hasDerivAt_logTraceTerm (A : Matrix n n ℝ) (k : ℕ) (z : ℝ) :
    HasDerivAt (logTraceTerm A k) (z ^ k * (A ^ (k + 1)).trace) z := by
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  have h := ((hasDerivAt_pow (k + 1) z).mul_const
    (A ^ (k + 1)).trace).div_const (k + 1 : ℝ)
  have hcoef : ((k + 1 : ℕ) : ℝ) * z ^ (k + 1 - 1) * (A ^ (k + 1)).trace /
      (k + 1 : ℝ) = z ^ k * (A ^ (k + 1)).trace := by
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp [hk]
    <;> ring
  rw [hcoef] at h
  exact h

/-- A summable uniform bound on the derivatives of the trace logarithm terms. -/
theorem logTrace_derivative_bound (A : Matrix n n ℝ) {r z : ℝ}
    (hr : 0 < r) (hz : z ∈ Set.Ioo (-r) r) (k : ℕ) :
    ‖z ^ k * (A ^ (k + 1)).trace‖ ≤
      (‖traceCLM (n := n)‖ * ‖A‖) * (r * ‖A‖) ^ k := by
  have hzabs : |z| ≤ r := (abs_lt.mpr hz).le
  have htrace : ‖(A ^ (k + 1)).trace‖ ≤
      ‖traceCLM (n := n)‖ * ‖A‖ ^ (k + 1) := by
    exact (trace_norm_bound _).trans
      (mul_le_mul_of_nonneg_left (norm_pow_le' A (Nat.succ_pos k)) (norm_nonneg _))
  calc
    ‖z ^ k * (A ^ (k + 1)).trace‖ =
        |z| ^ k * ‖(A ^ (k + 1)).trace‖ := by
      rw [norm_mul, norm_pow, Real.norm_eq_abs]
    _ ≤ r ^ k * (‖traceCLM (n := n)‖ * ‖A‖ ^ (k + 1)) := by
      gcongr
    _ = (‖traceCLM (n := n)‖ * ‖A‖) * (r * ‖A‖) ^ k := by
      rw [mul_pow, pow_succ]
      ring

/-- Termwise differentiation of the trace logarithm on any certified interval. -/
theorem hasDerivAt_logTrace_on_interval (A : Matrix n n ℝ) {r z : ℝ}
    (hr : 0 < r) (hsmall : r * ‖A‖ < 1) (hz : z ∈ Set.Ioo (-r) r) :
    HasDerivAt (logTrace A)
      (∑' k : ℕ, z ^ k * (A ^ (k + 1)).trace) z := by
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  have hbound : Summable (fun k : ℕ =>
      (‖traceCLM (n := n)‖ * ‖A‖) * (r * ‖A‖) ^ k) :=
    (summable_geometric_of_lt_one (mul_nonneg hr.le (norm_nonneg A)) hsmall).mul_left _
  have hzero : (0 : ℝ) ∈ Set.Ioo (-r) r := by
    constructor <;> linarith
  change HasDerivAt (fun y : ℝ => ∑' k : ℕ, logTraceTerm A k y)
    (∑' k : ℕ, z ^ k * (A ^ (k + 1)).trace) z
  exact hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    hbound isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => hasDerivAt_logTraceTerm A k y)
    (fun k y hy => logTrace_derivative_bound A hr hy k)
    hzero (by simp [logTraceTerm]) hz

/-- The trace logarithm series itself is summable on each certified interval. -/
theorem summable_logTrace_on_interval (A : Matrix n n ℝ) {r z : ℝ}
    (hr : 0 < r) (hsmall : r * ‖A‖ < 1) (hz : z ∈ Set.Ioo (-r) r) :
    Summable (fun k : ℕ => logTraceTerm A k z) := by
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  have hbound : Summable (fun k : ℕ =>
      (‖traceCLM (n := n)‖ * ‖A‖) * (r * ‖A‖) ^ k) :=
    (summable_geometric_of_lt_one (mul_nonneg hr.le (norm_nonneg A)) hsmall).mul_left _
  have hzero : (0 : ℝ) ∈ Set.Ioo (-r) r := by
    constructor <;> linarith
  exact summable_of_summable_hasDerivAt_of_isPreconnected (𝕜 := ℝ) (F := ℝ)
    hbound isOpen_Ioo isPreconnected_Ioo
    (fun k y _ => hasDerivAt_logTraceTerm A k y)
    (fun k y hy => logTrace_derivative_bound A hr hy k)
    hzero (by simp [logTraceTerm]) hz

/-- The general finite-matrix zeta identity on a certified interval. -/
theorem exp_logTrace_eq_zeta_on_interval (A : Matrix n n ℝ) {r z : ℝ}
    (hr : 0 < r) (hsmall : r * ‖A‖ < 1) (hz : z ∈ Set.Ioo (-r) r) :
    Real.exp (logTrace A z) = zeta A z := by
  have hnorm (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) : ‖y • A‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (abs_lt.mpr hy).le (norm_nonneg A)) hsmall
  have hsum (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
      HasDerivAt (logTrace A) ((1 - y • A)⁻¹ * A).trace y := by
    have h := hasDerivAt_logTrace_on_interval A hr hsmall hy
    rwa [(trace_resolvent_hasSum A y (hnorm y hy)).tsum_eq] at h
  let F : ℝ → ℝ := fun t => Real.exp (logTrace A t) * denominator A t
  have hprod (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) : HasDerivAt F 0 y := by
    have h := (hsum y hy).exp.mul
      (hasDerivAt_denominator A y (denominator_ne_zero_of_norm_lt_one A y (hnorm y hy)))
    convert h using 1 <;> ring
  have hzero : (0 : ℝ) ∈ Set.Ioo (-r) r := by
    constructor <;> linarith
  have heq : Set.EqOn F (fun _ => (1 : ℝ)) (Set.Ioo (-r) r) := by
    refine isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
      (fun y hy => (hprod y hy).differentiableAt.differentiableWithinAt)
      (by fun_prop) ?_ hzero ?_
    · intro y hy
      rw [(hprod y hy).deriv]
      simp
    · simp [F, logTrace_zero, denominator_zero]
  have h := heq hz
  dsimp [F] at h
  change Real.exp _ = (denominator A z)⁻¹
  rw [← one_div]
  exact (eq_div_iff (denominator_ne_zero_of_norm_lt_one A z (hnorm z hz))).mpr h

/-- Any point satisfying the strict norm condition lies in a larger certified interval. -/
theorem exists_trace_radius (c z : ℝ) (hc : 0 ≤ c) (hz : |z| * c < 1) :
    ∃ r : ℝ, 0 < r ∧ |z| < r ∧ r * c < 1 := by
  by_cases h0 : c = 0
  · refine ⟨|z| + 1, by positivity, by linarith, ?_⟩
    simp [h0]
  · have hcpos : 0 < c := by
      rcases lt_or_eq_of_le hc with h | h
      · exact h
      · exact (h0 h.symm).elim
    have hlt : |z| < 1 / c := (lt_div_iff₀ hcpos).2 hz
    obtain ⟨r, hzr, hr⟩ := exists_between hlt
    exact ⟨r, (abs_nonneg z).trans_lt hzr, hzr, (lt_div_iff₀ hcpos).1 hr⟩

/-- Convergence of the trace logarithm under the matrix norm condition. -/
theorem logTrace_hasSum (A : Matrix n n ℝ) (z : ℝ) (hz : ‖z • A‖ < 1) :
    HasSum (fun k : ℕ => logTraceTerm A k z) (logTrace A z) := by
  have hsmall : |z| * ‖A‖ < 1 := by simpa only [norm_smul, Real.norm_eq_abs] using hz
  obtain ⟨r, hr, hzr, hsmallr⟩ := exists_trace_radius ‖A‖ z (norm_nonneg A) hsmall
  exact (summable_logTrace_on_interval A hr hsmallr (abs_lt.mp hzr)).hasSum

/-- The general trace–determinant zeta identity for finite real matrices. -/
theorem exp_logTrace_eq_zeta (A : Matrix n n ℝ) (z : ℝ) (hz : ‖z • A‖ < 1) :
    Real.exp (logTrace A z) = zeta A z := by
  have hsmall : |z| * ‖A‖ < 1 := by simpa only [norm_smul, Real.norm_eq_abs] using hz
  obtain ⟨r, hr, hzr, hsmallr⟩ := exists_trace_radius ‖A‖ z (norm_nonneg A) hsmall
  exact exp_logTrace_eq_zeta_on_interval A hr hsmallr (abs_lt.mp hzr)

/-- The trace–determinant formula with its full convergent series displayed. -/
theorem exp_trace_series_eq_inv_det (A : Matrix n n ℝ) (z : ℝ) (hz : ‖z • A‖ < 1) :
    Real.exp (∑' k : ℕ, z ^ (k + 1) * (A ^ (k + 1)).trace / (k + 1 : ℝ)) =
      ((1 - z • A).det)⁻¹ := by
  exact exp_logTrace_eq_zeta A z hz

end Neoplatonic.LTR.TraceDeterminant
