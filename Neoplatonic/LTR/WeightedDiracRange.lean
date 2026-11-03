import Neoplatonic.LTR.EuclideanDiracSquaredResolvent
import Neoplatonic.LTR.InfiniteBlockCoordinates

/-!
# Uniform weighted Dirac block bounds

For a real symmetric Dirac block D with D² = (m²+s²)I,
its squared-resolvent weight w = (1+m²+s²)⁻¹ satisfies

  ‖D(w • v)‖ ≤ ‖v‖,
  ‖D(D(w • v))‖ ≤ ‖v‖.

The estimates are uniform over the mass and coupling coefficients,
including when either coefficient is unbounded across blocks.
They are the analytic input for the maximal-domain Hilbert proof.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The squared Dirac coefficient times its inverse weight is ≤ 1. -/
theorem diracSquareWeight_mul_le_one (mass scale : ℝ) :
    (mass ^ 2 + scale ^ 2) *
      (1 + mass ^ 2 + scale ^ 2)⁻¹ ≤ 1 := by
  have hpos : 0 < (1 : ℝ) + mass ^ 2 + scale ^ 2 := by positivity
  have h : (mass ^ 2 + scale ^ 2) /
      (1 + mass ^ 2 + scale ^ 2) ≤ 1 := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [sq_nonneg mass, sq_nonneg scale]
  simpa only [div_eq_mul_inv] using h

/-- The squared-resolvent coefficient lies in the interval [0,1]. -/
theorem diracSquareWeight_le_one (mass scale : ℝ) :
    (1 + mass ^ 2 + scale ^ 2)⁻¹ ≤ (1 : ℝ) := by
  have hpos : 0 < (1 : ℝ) + mass ^ 2 + scale ^ 2 := by positivity
  have h : (1 : ℝ) / (1 + mass ^ 2 + scale ^ 2) ≤ 1 := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [sq_nonneg mass, sq_nonneg scale]
  simpa only [one_div] using h

/-- The weighted square coefficient satisfies μ² w² ≤ 1. -/
theorem diracSquareWeight_sq_le_one (mass scale : ℝ) :
    (mass ^ 2 + scale ^ 2) *
      ((1 + mass ^ 2 + scale ^ 2)⁻¹) ^ 2 ≤ 1 := by
  let a : ℝ := mass ^ 2 + scale ^ 2
  let w : ℝ := (1 + mass ^ 2 + scale ^ 2)⁻¹
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hwle : w ≤ 1 := diracSquareWeight_le_one mass scale
  have haw : a * w ≤ 1 := diracSquareWeight_mul_le_one mass scale
  have hmul := mul_le_mul_of_nonneg_left hwle (mul_nonneg ha hw)
  change (a * w) * w ≤ (a * w) * 1 at hmul
  change a * w ^ 2 ≤ 1
  nlinarith

/-- Exact real Hilbert norm identity for the concrete Euclidean Dirac
block: norm(Dv)² = (m²+s²) norm(v)². -/
theorem euclideanDiracBlock_norm_sq
    (mass scale : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖euclideanDiracBlock mass scale v‖ ^ 2 =
      (mass ^ 2 + scale ^ 2) * ‖v‖ ^ 2 := by
  let D := euclideanDiracBlock mass scale
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (euclideanDiracBlock_isSelfAdjoint mass scale)
  calc
    ‖D v‖ ^ 2 = inner ℝ (D v) (D v) :=
      (real_inner_self_eq_norm_sq (D v)).symm
    _ = inner ℝ v (D (D v)) := hsym v (D v)
    _ = inner ℝ v ((mass ^ 2 + scale ^ 2) • v) := by
      rw [euclideanDiracBlock_square]
    _ = (mass ^ 2 + scale ^ 2) * ‖v‖ ^ 2 := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- Uniform norm bound on a Dirac block after the squared resolvent. -/
theorem weightedEuclideanDiracBlock_norm_le
    (mass scale : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖euclideanDiracBlock mass scale
      ((1 + mass ^ 2 + scale ^ 2)⁻¹ • v)‖ ≤ ‖v‖ := by
  let w : ℝ := (1 + mass ^ 2 + scale ^ 2)⁻¹
  let a : ℝ := mass ^ 2 + scale ^ 2
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hcoef : a * w ^ 2 ≤ 1 := diracSquareWeight_sq_le_one mass scale
  have hnorm : ‖w • v‖ = w * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  have henergy := euclideanDiracBlock_norm_sq mass scale (w • v)
  rw [hnorm] at henergy
  have hsq : ‖euclideanDiracBlock mass scale (w • v)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [henergy]
    calc
      a * (w * ‖v‖) ^ 2 = (a * w ^ 2) * ‖v‖ ^ 2 := by ring
      _ ≤ 1 * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = ‖v‖ ^ 2 := one_mul _
  change ‖euclideanDiracBlock mass scale (w • v)‖ ≤ ‖v‖
  nlinarith [norm_nonneg (euclideanDiracBlock mass scale (w • v)), norm_nonneg v]

/-- Uniform bound on the twice-applied block after its squared weight. -/
theorem weightedEuclideanDiracBlock_square_norm_le
    (mass scale : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖euclideanDiracBlock mass scale
      (euclideanDiracBlock mass scale
        ((1 + mass ^ 2 + scale ^ 2)⁻¹ • v))‖ ≤ ‖v‖ := by
  let w : ℝ := (1 + mass ^ 2 + scale ^ 2)⁻¹
  let a : ℝ := mass ^ 2 + scale ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have haw : a * w ≤ 1 := diracSquareWeight_mul_le_one mass scale
  have haw0 : 0 ≤ a * w := mul_nonneg ha hw
  have hblock :
      euclideanDiracBlock mass scale
        (euclideanDiracBlock mass scale (w • v)) = (a * w) • v := by
    rw [map_smul, map_smul, euclideanDiracBlock_square, smul_smul]
    rw [mul_comm w a]
  change ‖euclideanDiracBlock mass scale
    (euclideanDiracBlock mass scale (w • v))‖ ≤ ‖v‖
  rw [hblock, norm_smul, Real.norm_eq_abs, abs_of_nonneg haw0]
  calc
    (a * w) * ‖v‖ ≤ 1 * ‖v‖ :=
      mul_le_mul_of_nonneg_right haw (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/-- The already-proved compact squared-resolvent candidate maps every
Hilbert vector into the maximal domain of the actual unbounded D. -/
theorem chosenSquaredResolvent_mem_maximalDiracDomain
    (scale : ℕ → ℝ) (ψ : DiracBlockHilbert) :
    chosenSquaredResolventCLM scale ψ ∈
      maximalDiracDomain (fun j => (2 : ℝ) ^ j) scale := by
  change Memℓp
    (diracBlockwise (fun j => (2 : ℝ) ^ j) scale
      (chosenSquaredResolventCLM scale ψ)) 2
  apply (lp.memℓp ψ).mono'
  intro j
  change ‖euclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      ((chosenSquaredResolventCLM scale ψ) j)‖ ≤ ‖ψ j‖
  rw [chosenSquaredResolventCLM_apply]
  exact weightedEuclideanDiracBlock_norm_le ((2 : ℝ) ^ j) (scale j) (ψ j)

end Neoplatonic.LTR
