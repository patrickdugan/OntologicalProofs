import Neoplatonic.LTR.ComplexOrdinaryResolventGlobal

/-!
# Exponential decay of complex ordinary Dirac resolvent blocks

For each real m≥1, the Dirac block D(m,s) has
‖D(m,s) ((1+m²+s²)⁻¹ • v)‖ ≤ m⁻¹ ‖v‖.
The scalar weight is itself ≤ m⁻¹. Hence the ordinary complex
resolvent block Q_j=(D_j+iI)/(1+4^j+s_j²) satisfies
‖Q_j‖≤2/(2^j), giving a uniform estimate for every tail j≥N.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- For mass≥1, the squared-resolvent weight is at most mass⁻¹. -/
theorem diracSquaredWeight_le_invMass
    (mass scale : ℝ) (hm : 1 ≤ mass) :
    (1 + mass ^ 2 + scale ^ 2)⁻¹ ≤ mass⁻¹ := by
  have hmpos : 0 < mass := lt_of_lt_of_le (by norm_num) hm
  have hm2 : mass ≤ mass ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hmpos) (sub_nonneg.mpr hm)]
  have hden : mass ≤ 1 + mass ^ 2 + scale ^ 2 := by
    nlinarith [sq_nonneg scale]
  have h := one_div_le_one_div_of_le hmpos hden
  simpa only [one_div] using h

/-- The weighted Dirac block has squared norm bounded by mass⁻²
times the input norm squared. -/
theorem diracSquaredEnergyWeight_le_invMass_sq
    (mass scale : ℝ) (hm : 1 ≤ mass) :
    (mass ^ 2 + scale ^ 2) *
      ((1 + mass ^ 2 + scale ^ 2)⁻¹) ^ 2 ≤ (mass⁻¹) ^ 2 := by
  let w : ℝ := (1 + mass ^ 2 + scale ^ 2)⁻¹
  let a : ℝ := mass ^ 2 + scale ^ 2
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have haw : a * w ≤ 1 := diracSquareWeight_mul_le_one mass scale
  have hmpos : 0 < mass := lt_of_lt_of_le (by norm_num) hm
  have hmass_sq_pos : 0 < mass ^ 2 := sq_pos_of_pos hmpos
  have hden : mass ^ 2 ≤ 1 + mass ^ 2 + scale ^ 2 := by
    nlinarith [sq_nonneg scale]
  have hwle : w ≤ (mass ^ 2)⁻¹ := by
    dsimp [w]
    simpa only [one_div] using
      (one_div_le_one_div_of_le hmass_sq_pos hden)
  have h1 : a * w ^ 2 ≤ w := by
    calc
      a * w ^ 2 = (a * w) * w := by ring
      _ ≤ 1 * w := mul_le_mul_of_nonneg_right haw hw
      _ = w := one_mul _
  change a * w ^ 2 ≤ (mass⁻¹)^2
  calc
    a * w ^ 2 ≤ w := h1
    _ ≤ (mass ^ 2)⁻¹ := hwle
    _ = (mass⁻¹)^2 := by rw [inv_pow]

/-- The weighted complex Dirac norm decays by the inverse mass. -/
theorem weightedComplexDiracBlock_norm_le_invMass
    (mass scale : ℝ) (hm : 1 ≤ mass)
    (v : EuclideanSpace ℂ (Fin 2)) :
    ‖complexEuclideanDiracBlock mass scale
      (((1 + mass ^ 2 + scale ^ 2)⁻¹ : ℝ) • v)‖ ≤
      mass⁻¹ * ‖v‖ := by
  let w : ℝ := (1 + mass ^ 2 + scale ^ 2)⁻¹
  let a : ℝ := mass ^ 2 + scale ^ 2
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hmpos : 0 < mass := lt_of_lt_of_le (by norm_num) hm
  have hcoef : a * w ^ 2 ≤ (mass⁻¹)^2 :=
    diracSquaredEnergyWeight_le_invMass_sq mass scale hm
  have hnorm : ‖(w : ℂ) • v‖ = w * ‖v‖ := by
    rw [norm_smul]
    simp [hw]
  have henergy := complexEuclideanDiracBlock_norm_sq mass scale ((w : ℂ) • v)
  rw [hnorm] at henergy
  have hsq :
      ‖complexEuclideanDiracBlock mass scale ((w : ℂ) • v)‖ ^ 2 ≤
      (mass⁻¹ * ‖v‖) ^ 2 := by
    rw [henergy]
    calc
      a * (w * ‖v‖)^2 = (a * w ^ 2) * ‖v‖ ^ 2 := by ring
      _ ≤ (mass⁻¹)^2 * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = (mass⁻¹ * ‖v‖)^2 := by ring
  change ‖complexEuclideanDiracBlock mass scale ((w : ℂ) • v)‖ ≤
    mass⁻¹ * ‖v‖
  have hc : 0 ≤ mass⁻¹ * ‖v‖ :=
    mul_nonneg (inv_nonneg.mpr (le_of_lt hmpos)) (norm_nonneg v)
  nlinarith [norm_nonneg (complexEuclideanDiracBlock mass scale ((w : ℂ) • v))]

/-- The ordinary complex resolvent block has exponentially decaying
operator norm, uniformly in its arbitrary off-diagonal scale. -/
theorem complexOrdinaryResolventBlock_norm_le_invPow
    (scale : ℕ → ℝ) (j : ℕ) :
    ‖complexOrdinaryResolventBlock scale j‖ ≤
      2 * ((2 : ℝ)^j)⁻¹ := by
  have hm : (1 : ℝ) ≤ (2 : ℝ)^j := one_le_pow₀ (by norm_num)
  have hmpos : 0 < (2 : ℝ)^j := by positivity
  have hbound : 0 ≤ 2 * ((2 : ℝ)^j)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr (le_of_lt hmpos))
  apply ContinuousLinearMap.opNorm_le_bound _ hbound
  intro v
  let mass : ℝ := (2 : ℝ)^j
  let w : ℝ := chosenSquaredResolventWeight scale j
  have hw : 0 ≤ w := chosenSquaredResolventWeight_nonneg scale j
  have hwle : w ≤ mass⁻¹ :=
    diracSquaredWeight_le_invMass mass (scale j) hm
  have hnorm : ‖Complex.I • ((w : ℂ) • v)‖ = w * ‖v‖ := by
    rw [norm_smul, norm_smul]
    simp [hw]
  rw [complexOrdinaryResolventBlock_apply]
  calc
    ‖complexEuclideanDiracBlock mass (scale j) ((w : ℂ) • v) +
        Complex.I • ((w : ℂ) • v)‖ ≤
      ‖complexEuclideanDiracBlock mass (scale j) ((w : ℂ) • v)‖ +
      ‖Complex.I • ((w : ℂ) • v)‖ := norm_add_le _ _
    _ ≤ mass⁻¹ * ‖v‖ + mass⁻¹ * ‖v‖ :=
      add_le_add
        (weightedComplexDiracBlock_norm_le_invMass mass (scale j) hm v)
        (by
          rw [hnorm]
          exact mul_le_mul_of_nonneg_right hwle (norm_nonneg v))
    _ = (2 * mass⁻¹) * ‖v‖ := by ring

/-- Uniform tail norm for each Q_j at j≥N. -/
theorem complexOrdinaryResolventBlock_norm_le_tail
    (scale : ℕ → ℝ) (N j : ℕ) (hNj : N ≤ j) :
    ‖complexOrdinaryResolventBlock scale j‖ ≤
      2 * ((2 : ℝ)^N)⁻¹ := by
  have hp : (2 : ℝ)^N ≤ (2 : ℝ)^j :=
    pow_le_pow_right₀ (by norm_num) hNj
  have hi : ((2 : ℝ)^j)⁻¹ ≤ ((2 : ℝ)^N)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ)^N) hp)
  exact (complexOrdinaryResolventBlock_norm_le_invPow scale j).trans
    (mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2))

end Neoplatonic.LTR
