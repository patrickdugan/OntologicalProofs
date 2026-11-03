import Neoplatonic.LTR.ComplexOrdinaryResolventBlock

/-!
# Ordinary Dirac resolvent as a bounded complex Hilbert-space operator

The block inverses Q_j=(D_j+iI)/(1+4^j+s_j²) are uniformly bounded
by 2. Mathlib's lp.mapCLM thus produces their direct sum Q on the
actual infinite complex Hilbert space. Its range lies in Dom(D).
Two-sided inverse equations identify Q with (D-iI)⁻¹.

The separate compactness proof uses finite-rank truncations and
the decaying norm bound on the ordinary resolvent's high blocks.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The chosen squared-resolvent coefficient is at most one. -/
theorem chosenSquaredResolventWeight_le_one
    (scale : ℕ → ℝ) (j : ℕ) :
    chosenSquaredResolventWeight scale j ≤ 1 := by
  have hj := chosenSquaredResolventWeight_le_tail scale j
  apply hj.trans
  unfold squaredResolventTail
  have hbase : (1 : ℝ) ≤ 1 + (4 : ℝ)^j := by
    have hp : 0 ≤ (4 : ℝ)^j := pow_nonneg (by norm_num) j
    linarith
  have hle := one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 1) hbase
  simpa [one_div] using hle

/-- Each complex ordinary resolvent block has operator norm at most 2. -/
theorem complexOrdinaryResolventBlock_norm_le
    (scale : ℕ → ℝ) (j : ℕ) :
    ‖complexOrdinaryResolventBlock scale j‖ ≤ (2 : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 2)
  intro v
  let w : ℝ := chosenSquaredResolventWeight scale j
  have hw : 0 ≤ w := chosenSquaredResolventWeight_nonneg scale j
  have hwle : w ≤ 1 := chosenSquaredResolventWeight_le_one scale j
  have hnorm : ‖Complex.I • ((w : ℂ) • v)‖ = w * ‖v‖ := by
    rw [norm_smul, norm_smul]
    simp [hw]
  rw [complexOrdinaryResolventBlock_apply]
  calc
    ‖complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
        ((w : ℂ) • v) + Complex.I • ((w : ℂ) • v)‖ ≤
      ‖complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j) ((w : ℂ) • v)‖ +
      ‖Complex.I • ((w : ℂ) • v)‖ := norm_add_le _ _
    _ ≤ ‖v‖ + ‖v‖ := add_le_add
      (weightedComplexEuclideanDiracBlock_norm_le ((2 : ℝ) ^ j) (scale j) v)
      (by
        rw [hnorm]
        exact (mul_le_mul_of_nonneg_right hwle (norm_nonneg v)).trans_eq (one_mul _))
    _ = 2 * ‖v‖ := by ring

/-- The actual bounded ordinary resolvent candidate on H_C. -/
noncomputable def chosenComplexOrdinaryResolventCLM (scale : ℕ → ℝ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  lp.mapCLM 2 (fun j => complexOrdinaryResolventBlock scale j)
    (by norm_num : (0 : ℝ) ≤ 2)
    (fun j => complexOrdinaryResolventBlock_norm_le scale j)

/-- Its jth coordinate is exactly Q_j applied to the jth input. -/
theorem chosenComplexOrdinaryResolventCLM_apply
    (scale : ℕ → ℝ) (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    chosenComplexOrdinaryResolventCLM scale ψ j =
      complexOrdinaryResolventBlock scale j (ψ j) := by
  change complexOrdinaryResolventBlock scale j (ψ j) = _
  rfl

set_option maxHeartbeats 1000000 in
/-- Uniform bound on D_j Q_j from the weighted D and D² estimates. -/
theorem complexOrdinaryResolventBlock_D_norm_le
    (scale : ℕ → ℝ) (j : ℕ)
    (v : EuclideanSpace ℂ (Fin 2)) :
    ‖complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      (complexOrdinaryResolventBlock scale j v)‖ ≤ 2 * ‖v‖ := by
  let D := complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
  let w : ℂ := ((chosenSquaredResolventWeight scale j : ℝ) : ℂ)
  have hformula : D (complexOrdinaryResolventBlock scale j v) =
      D (D (w • v)) + Complex.I • (D (w • v)) := by
    rw [complexOrdinaryResolventBlock_apply, map_add]
    simp only [map_smul]
    dsimp only [w]
  rw [hformula]
  have hnormI :
      ‖Complex.I • (D (w • v))‖ = ‖D (w • v)‖ := by
    rw [norm_smul]
    simp
  calc
    ‖D (D (w • v)) + Complex.I • (D (w • v))‖ ≤
      ‖D (D (w • v))‖ + ‖Complex.I • (D (w • v))‖ :=
      norm_add_le _ _
    _ ≤ ‖v‖ + ‖v‖ := add_le_add
      (weightedComplexEuclideanDiracBlock_square_norm_le ((2 : ℝ) ^ j) (scale j) v)
      (by rw [hnormI]; exact weightedComplexEuclideanDiracBlock_norm_le ((2 : ℝ) ^ j) (scale j) v)
    _ = 2 * ‖v‖ := by ring

/-- Every Hilbert vector mapped by Q lies in the domain of D. -/
theorem chosenComplexOrdinaryResolvent_mem_maximalComplexDiracDomain
    (scale : ℕ → ℝ) (ψ : ComplexDiracBlockHilbert) :
    chosenComplexOrdinaryResolventCLM scale ψ ∈
      maximalComplexDiracDomain (fun j => (2 : ℝ) ^ j) scale := by
  change Memℓp (complexDiracBlockwise (fun j => (2 : ℝ) ^ j) scale
    (chosenComplexOrdinaryResolventCLM scale ψ)) 2
  have hψ : Memℓp (fun j : ℕ => (2 : ℂ) • ψ j) 2 :=
    (lp.memℓp ψ).const_smul (2 : ℂ)
  apply hψ.mono'
  intro j
  change ‖complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
    ((chosenComplexOrdinaryResolventCLM scale ψ) j)‖ ≤
      ‖(2 : ℂ) • ψ j‖
  rw [chosenComplexOrdinaryResolventCLM_apply]
  simpa [norm_smul] using complexOrdinaryResolventBlock_D_norm_le scale j (ψ j)

/-- The bounded Q is the right inverse of the unbounded D-i on H_C. -/
theorem chosenComplexOrdinaryResolvent_right_inverse
    (scale : ℕ → ℝ) (ψ : ComplexDiracBlockHilbert) :
    (maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale)
      ⟨chosenComplexOrdinaryResolventCLM scale ψ,
        chosenComplexOrdinaryResolvent_mem_maximalComplexDiracDomain scale ψ⟩ -
      Complex.I • chosenComplexOrdinaryResolventCLM scale ψ = ψ := by
  apply lp.ext
  funext j
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply]
  rw [chosenComplexOrdinaryResolventCLM_apply]
  change complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      (complexOrdinaryResolventBlock scale j (ψ j)) -
      Complex.I • complexOrdinaryResolventBlock scale j (ψ j) = ψ j
  exact complexOrdinaryResolventBlock_right_inverse scale j (ψ j)

/-- The bounded Q is the left inverse of D-i on the precise maximal domain. -/
theorem chosenComplexOrdinaryResolvent_left_inverse
    (scale : ℕ → ℝ) (ψ : ComplexDiracBlockHilbert)
    (hψ : ψ ∈ maximalComplexDiracDomain (fun j => (2 : ℝ) ^ j) scale) :
    chosenComplexOrdinaryResolventCLM scale
      ((maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale) ⟨ψ,hψ⟩ -
        Complex.I • ψ) = ψ := by
  apply lp.ext
  funext j
  rw [chosenComplexOrdinaryResolventCLM_apply]
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply]
  change complexOrdinaryResolventBlock scale j
      (complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j) (ψ j) -
        Complex.I • ψ j) = ψ j
  exact complexOrdinaryResolventBlock_left_inverse scale j (ψ j)

end Neoplatonic.LTR
