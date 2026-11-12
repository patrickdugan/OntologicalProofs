import Neoplatonic.LTR.SixDimensionalPerturbedThreeChannelNorm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-155: robust four-channel C*-norm obstruction with a fourth Dirac edge

MAN-154 exposes the 01/10 opposite-neutral edge J in the genuine
nonsaturated six-dimensional coordinate commutator:
  A = H+E01+E32+J, B = H+E02+E31-J.

The MAN-153 quantitative three-channel C*-norm theorem gives a
squared-norm upper bound for the common corner H and two
mutually orthogonal Hermitian neutral edges E,F, even if their
products with H are only approximately zero.

Here we retain the extra edge J using the triangle inequality.
If ||J||<=delta, and
   ||H||<=1/2,
   ||E||²,||F||²<=1/2+eta,
   ||HE||,||HF||<=kappa,
then the four-channel operator norm is strictly below one when
   eta + 4*kappa + 2*delta + delta² < 1/4.

This exposes a precise fourth-channel error budget to be discharged
with original opposite-block energy E12 in the nonsaturated case.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A perturbed Hermitian three-channel operator with an extra
bounded fourth edge has a robust strict subunit operator norm. -/
theorem sixMatrix_fourChannel_perturbed_halfEnergy_norm_lt_one
    (H E F J : SixMat)
    (hH : H.IsHermitian) (hE : E.IsHermitian)
    (hF : F.IsHermitian)
    (hEF : E * F = 0)
    (hHbound : ‖H‖ ≤ (1 / 2 : ℝ))
    (eta kappa delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hEbound : ‖E‖ * ‖E‖ ≤ (1 / 2 : ℝ) + eta)
    (hFbound : ‖F‖ * ‖F‖ ≤ (1 / 2 : ℝ) + eta)
    (hHE : ‖H * E‖ ≤ kappa)
    (hHF : ‖H * F‖ ≤ kappa)
    (hJ : ‖J‖ ≤ delta)
    (hbudget : eta + 4 * kappa + 2 * delta + delta * delta <
      (1 / 4 : ℝ)) :
    ‖H + E + F + J‖ < (1 : ℝ) := by
  let G : SixMat := H + E + F
  have hHsq : ‖H‖ * ‖H‖ ≤ (1 / 4 : ℝ) := by
    nlinarith [norm_nonneg H]
  have hEFsq :
      max ‖E‖ ‖F‖ * max ‖E‖ ‖F‖ ≤
        (1 / 2 : ℝ) + eta := by
    rcases le_total ‖E‖ ‖F‖ with hle | hle
    · rw [max_eq_right hle]
      exact hFbound
    · rw [max_eq_left hle]
      exact hEbound
  have hThree := sixMatrix_threeChannel_perturbed_normSq_le
    H E F hH hE hF hEF
  have hGsq : ‖G‖ * ‖G‖ ≤
      (3 / 4 : ℝ) + eta + 4 * kappa := by
    dsimp [G]
    nlinarith [hThree, hHsq, hEFsq, hHE, hHF]
  have hSmall : (3 / 4 : ℝ) + eta + 4 * kappa < 1 := by
    nlinarith [sq_nonneg delta]
  have hGsmall : ‖G‖ < (1 : ℝ) := by
    nlinarith [norm_nonneg G, hGsq]
  have hGnonneg : 0 ≤ ‖G‖ := norm_nonneg G
  have hJG : ‖G + J‖ ≤ ‖G‖ + delta :=
    (norm_add_le G J).trans (add_le_add_left hJ _)
  have hprod :
      0 ≤ (‖G‖ + delta - ‖G + J‖) *
        (‖G‖ + delta + ‖G + J‖) :=
    mul_nonneg (by linarith)
      (by positivity)
  have hgap :
      0 ≤ (1 - ‖G‖) * delta :=
    mul_nonneg (by linarith) hdelta
  have hFoursq :
      ‖G + J‖ * ‖G + J‖ ≤
        (3 / 4 : ℝ) + eta + 4 * kappa +
          2 * delta + delta * delta := by
    nlinarith [hprod, hgap, hGsq]
  have hEq : H + E + F + J = G + J := rfl
  rw [hEq]
  nlinarith [norm_nonneg (G + J), hFoursq]

/-- Repackage the quantitative gate directly as an obstruction to
the Hamming-forced unit lower bound. -/
theorem sixMatrix_fourChannel_perturbed_unitNorm_impossible
    (H E F J : SixMat)
    (hH : H.IsHermitian) (hE : E.IsHermitian)
    (hF : F.IsHermitian)
    (hEF : E * F = 0)
    (hHbound : ‖H‖ ≤ (1 / 2 : ℝ))
    (eta kappa delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hEbound : ‖E‖ * ‖E‖ ≤ (1 / 2 : ℝ) + eta)
    (hFbound : ‖F‖ * ‖F‖ ≤ (1 / 2 : ℝ) + eta)
    (hHE : ‖H * E‖ ≤ kappa)
    (hHF : ‖H * F‖ ≤ kappa)
    (hJ : ‖J‖ ≤ delta)
    (hbudget : eta + 4 * kappa + 2 * delta + delta * delta <
      (1 / 4 : ℝ))
    (hUnit : (1 : ℝ) ≤ ‖H + E + F + J‖) :
    False := by
  have hlt := sixMatrix_fourChannel_perturbed_halfEnergy_norm_lt_one
    H E F J hH hE hF hEF hHbound
    eta kappa delta hdelta hEbound hFbound
    hHE hHF hJ hbudget
  linarith

end Neoplatonic.LTR
