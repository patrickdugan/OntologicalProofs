import Neoplatonic.LTR.ComplexSquaredResolventCompact
import Neoplatonic.LTR.WeightedDiracRange

/-!
# Complex weighted Dirac energy and squared-resolvent domain bounds

Real masses and couplings define complex Hermitian 2×2 blocks D_j.
Their exact squared-energy identity gives uniform bounds on D_j w_j
and D_j² w_j, for w_j = (1 + 4^j + s_j²)⁻¹.
The first bound proves that R_C sends the whole complex Hilbert space
into the maximal domain of the unbounded D_C.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Exact squared energy for the complex Hilbert Dirac block. -/
theorem complexEuclideanDiracBlock_norm_sq
    (mass scale : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖complexEuclideanDiracBlock mass scale v‖ ^ 2 =
      (mass ^ 2 + scale ^ 2) * ‖v‖ ^ 2 := by
  let D := complexEuclideanDiracBlock mass scale
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (complexEuclideanDiracBlock_isSelfAdjoint mass scale)
  calc
    ‖D v‖ ^ 2 = Complex.re (inner ℂ (D v) (D v)) :=
      by simpa only using (norm_sq_eq_re_inner (D v))
    _ = Complex.re (inner ℂ v (D (D v))) := congrArg Complex.re (hsym v (D v))
    _ = Complex.re (inner ℂ v
        (((mass ^ 2 + scale ^ 2 : ℝ) : ℂ) • v)) := by
      rw [complexEuclideanDiracBlock_square]
    _ = (mass ^ 2 + scale ^ 2) * ‖v‖ ^ 2 := by
      rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
      rw [← Complex.ofReal_mul, Complex.ofReal_re]

/-- Uniform norm bound for one complex Dirac block composed with w. -/
theorem weightedComplexEuclideanDiracBlock_norm_le
    (mass scale : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖complexEuclideanDiracBlock mass scale
      (((1 + mass ^ 2 + scale ^ 2)⁻¹ : ℝ) • v)‖ ≤ ‖v‖ := by
  let w : ℝ := (1 + mass ^ 2 + scale ^ 2)⁻¹
  let a : ℝ := mass ^ 2 + scale ^ 2
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hcoef : a * w ^ 2 ≤ 1 := diracSquareWeight_sq_le_one mass scale
  have hnorm : ‖(w : ℂ) • v‖ = w * ‖v‖ := by
    rw [norm_smul]
    simp [hw]
  have henergy := complexEuclideanDiracBlock_norm_sq mass scale ((w : ℂ) • v)
  rw [hnorm] at henergy
  have hsq :
      ‖complexEuclideanDiracBlock mass scale ((w : ℂ) • v)‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [henergy]
    calc
      a * (w * ‖v‖) ^ 2 = (a * w ^ 2) * ‖v‖ ^ 2 := by ring
      _ ≤ 1 * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
      _ = ‖v‖ ^ 2 := one_mul _
  change ‖complexEuclideanDiracBlock mass scale ((w : ℂ) • v)‖ ≤ ‖v‖
  nlinarith [norm_nonneg (complexEuclideanDiracBlock mass scale ((w : ℂ) • v)),
    norm_nonneg v]

/-- Uniform norm bound for D² applied to the inverse-weighted block. -/
theorem weightedComplexEuclideanDiracBlock_square_norm_le
    (mass scale : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    ‖complexEuclideanDiracBlock mass scale
      (complexEuclideanDiracBlock mass scale
        (((1 + mass ^ 2 + scale ^ 2)⁻¹ : ℝ) • v))‖ ≤ ‖v‖ := by
  let w : ℝ := (1 + mass ^ 2 + scale ^ 2)⁻¹
  let a : ℝ := mass ^ 2 + scale ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have haw : a * w ≤ 1 := diracSquareWeight_mul_le_one mass scale
  have haw0 : 0 ≤ a * w := mul_nonneg ha hw
  have hblock :
      complexEuclideanDiracBlock mass scale
        (complexEuclideanDiracBlock mass scale ((w : ℂ) • v)) =
          (((a * w : ℝ) : ℂ)) • v := by
    rw [map_smul, map_smul, complexEuclideanDiracBlock_square, smul_smul]
    congr 1
    norm_cast
    ring
  change ‖complexEuclideanDiracBlock mass scale
    (complexEuclideanDiracBlock mass scale ((w : ℂ) • v))‖ ≤ ‖v‖
  rw [hblock, norm_smul]
  have hnorm : ‖((a * w : ℝ) : ℂ)‖ = a * w := by simp [ha, hw]
  rw [hnorm]
  calc
    (a * w) * ‖v‖ ≤ 1 * ‖v‖ :=
      mul_le_mul_of_nonneg_right haw (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/-- The compact complex squared-resolvent candidate maps the full
complex Hilbert space into the actual maximal unbounded Dirac domain. -/
theorem chosenComplexSquaredResolvent_mem_maximalComplexDiracDomain
    (scale : ℕ → ℝ) (ψ : ComplexDiracBlockHilbert) :
    chosenComplexSquaredResolventCLM scale ψ ∈
      maximalComplexDiracDomain (fun j => (2 : ℝ) ^ j) scale := by
  change Memℓp
    (complexDiracBlockwise (fun j => (2 : ℝ) ^ j) scale
      (chosenComplexSquaredResolventCLM scale ψ)) 2
  apply (lp.memℓp ψ).mono'
  intro j
  change ‖complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      ((chosenComplexSquaredResolventCLM scale ψ) j)‖ ≤ ‖ψ j‖
  rw [chosenComplexSquaredResolventCLM_apply]
  exact weightedComplexEuclideanDiracBlock_norm_le
    ((2 : ℝ) ^ j) (scale j) (ψ j)

end Neoplatonic.LTR
