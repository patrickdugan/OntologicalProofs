import Neoplatonic.LTR.SixDimensionalPauliOppositeEnergyRegions
import Mathlib.Tactic

/-!
# LTR-MAN-85: sharp spectral Pauli overlap from the signed eigenquartet

The genuine six-dimensional signed eigenquartet leaves a common
two-dimensional Hermitian traceless residual with Pauli quadratic
coefficients q, r and real mixed coefficient c.

MAN-72 already establishes:
  q ≥ 0, r ≥ 0, c² ≤ 4qr, q+r+|c| ≤ 1.

The Gram determinant then implies |c| ≤ q+r, giving the sharp
universal contraction bound |c| ≤ 1/2, independently of the six
truth-fibre multiplicity pattern. In particular, this tightens
MAN-84's exceptional signed energy intervals.

At the endpoint |c| = 1/2, equality forces q=r=1/4 and
c²=4qr. The Pauli Gram determinant vanishes, proving a rigid
collinearity condition on the true two-dimensional residual
Pauli vectors of the signed quartet.
-/

namespace Neoplatonic.LTR

private abbrev SixH := EuclideanSpace ℂ (Fin 6)

/-- Real positive-semidefinite two-vector Gram data and the
simultaneous contraction budget force a sharp half-unit
bound on the mixed coefficient. -/
theorem realGram_mixed_abs_le_half
    (q r c : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdet : c ^ 2 ≤ 4 * q * r)
    (hbudget : q + r + |c| ≤ 1) :
    |c| ≤ (1 / 2 : ℝ) := by
  have hsq : |c| ^ 2 ≤ (q + r) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (q - r)]
  have hle : |c| ≤ q + r :=
    (sq_le_sq₀ (abs_nonneg _) (add_nonneg hq hr)).mp hsq
  linarith

/-- Equality at the maximal spectral overlap forces both Pauli
quadratic lengths to be exactly one quarter. The Cauchy
determinant also saturates. -/
theorem realGram_half_saturation_rigid
    (q r c : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdet : c ^ 2 ≤ 4 * q * r)
    (hbudget : q + r + |c| ≤ 1)
    (hsat : |c| = (1 / 2 : ℝ)) :
    q = (1 / 4 : ℝ) ∧
    r = (1 / 4 : ℝ) ∧
    c ^ 2 = 4 * q * r := by
  have hsq : |c| ^ 2 ≤ (q + r) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (q - r)]
  have hle : |c| ≤ q + r :=
    (sq_le_sq₀ (abs_nonneg _) (add_nonneg hq hr)).mp hsq
  have hsum : q + r = (1 / 2 : ℝ) := by linarith
  have hcsq : c ^ 2 = (1 / 4 : ℝ) := by
    nlinarith [sq_abs c]
  have hsumSq : (q + r) ^ 2 = (1 / 4 : ℝ) := by
    rw [hsum]
    norm_num
  have hdiffSq : (q - r) ^ 2 ≤ 0 := by
    nlinarith [hdet, hsumSq, hcsq]
  have hqr : q = r := by
    nlinarith [sq_nonneg (q - r)]
  have hqval : q = (1 / 4 : ℝ) := by linarith
  have hrval : r = (1 / 4 : ℝ) := by linarith
  refine ⟨hqval, hrval, ?_⟩
  rw [hqval, hrval]
  norm_num [hcsq]

/-- The real Pauli mixed coefficient of any true six-dimensional
signed-quartet residual is bounded by 1/2. This uses MAN-72's
spectral Gram positivity and simultaneous residual contractions. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_pauliMixed_abs_le_half
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0) :
    |pauliRealMixed (S.sixDimResidualMatrixA hq (by simp))
       (S.sixDimResidualMatrixB hq (by simp))| ≤ (1 / 2 : ℝ) := by
  obtain ⟨hq0, hr0, hdet, hbudget⟩ :=
    S.sixDimResidual_realGram_cone hq (by simp) htrA htrB
  exact realGram_mixed_abs_le_half _ _ _ hq0 hr0 hdet hbudget

/-- Saturation of the actual residual mixed coefficient imposes
q=r=1/4 and equality in the residual Pauli Gram determinant. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_half_saturation_rigid
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0)
    (hsat : |pauliRealMixed
        (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp))| = (1 / 2 : ℝ)) :
    pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) = (1 / 4 : ℝ) ∧
    pauliRealQuadratic (S.sixDimResidualMatrixB hq (by simp)) = (1 / 4 : ℝ) ∧
    (pauliRealMixed (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp))) ^ 2 =
      4 * pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) *
        pauliRealQuadratic (S.sixDimResidualMatrixB hq (by simp)) := by
  obtain ⟨hq0, hr0, hdet, hbudget⟩ :=
    S.sixDimResidual_realGram_cone hq (by simp) htrA htrB
  exact realGram_half_saturation_rigid _ _ _ hq0 hr0 hdet hbudget hsat

end Neoplatonic.LTR
