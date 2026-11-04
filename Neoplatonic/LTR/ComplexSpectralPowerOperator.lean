import Neoplatonic.LTR.ComplexSpectralSummability
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Positive spectral powers on the actual infinite complex Dirac Hilbert space

For the maximal self-adjoint block Dirac D with masses 2^j,
its verified squared resolvent is the positive diagonal operator

  R = (I + D²)⁻¹,  R_j = (1 + 4^j + s_j²)⁻¹ I₂.

For p > 0, the real scalar coefficient
  w_p(j) = (1 + 4^j + s_j²)^(-p/2)
defines an actual bounded complex-linear operator on
H = ℓ²(ℕ, ℂ²), with norm at most one. The blockwise identity
and the finite-dimensional complex trace are recorded explicitly.

The total Hilbert-basis trace and convergence of the finite-rank
traces will be developed in the next module. Mathlib's finite
trace is defined on finite-dimensional endomorphisms.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Scalar coefficient of (I+D²)^(-p/2) on the j-th Dirac block. -/
noncomputable def complexSpectralPowerWeight
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) : ℝ :=
  (chosenSquaredResolventWeight scale j)^(p / 2)

theorem complexSpectralPowerWeight_nonneg
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    0 ≤ complexSpectralPowerWeight scale p j := by
  exact Real.rpow_nonneg
    (chosenSquaredResolventWeight_nonneg scale j) (p / 2)

theorem complexSpectralPowerWeight_le_one
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) (j : ℕ) :
    complexSpectralPowerWeight scale p j ≤ 1 := by
  unfold complexSpectralPowerWeight
  have hpow : (0 : ℝ) ≤ p / 2 := by linarith
  have h := Real.rpow_le_rpow
    (chosenSquaredResolventWeight_nonneg scale j)
    (chosenSquaredResolventWeight_le_one scale j) hpow
  simpa only [Real.one_rpow] using h

/-- The genuine positive diagonal spectral-power operator on the
infinite-dimensional complex Hilbert sum. -/
noncomputable def chosenComplexSpectralPowerCLM
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  complexBoundedBlockDiagonal
    (complexSpectralPowerWeight scale p) 1
    (by norm_num)
    (by
      intro j
      rw [abs_of_nonneg (complexSpectralPowerWeight_nonneg scale p j)]
      exact complexSpectralPowerWeight_le_one scale p hp j)

/-- Coordinate formula for the actual global operator. -/
theorem chosenComplexSpectralPowerCLM_apply
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    chosenComplexSpectralPowerCLM scale p hp ψ j =
      (complexSpectralPowerWeight scale p j : ℂ) • ψ j :=
  complexBoundedBlockDiagonal_apply _ _ _ _ ψ j

theorem chosenComplexSpectralPowerCLM_norm_le_one
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    ‖chosenComplexSpectralPowerCLM scale p hp‖ ≤ 1 :=
  complexBoundedBlockDiagonal_norm_le _ _ _ _

/-- The two-dimensional block of the global spectral-power map. -/
noncomputable def complexSpectralPowerBlockCLM
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  complexScalarBlockCLM (complexSpectralPowerWeight scale p j)

/-- The finite-dimensional complex trace of the j-th spectral-power
block is precisely the previously proved real trace contribution. -/
theorem complexSpectralPowerBlock_trace
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin 2))
      (complexSpectralPowerBlockCLM scale p j).toLinearMap =
      (complexSpectralTraceTerm scale p j : ℂ) := by
  let w := complexSpectralPowerWeight scale p j
  have hmap :
      (complexSpectralPowerBlockCLM scale p j).toLinearMap =
      (w : ℂ) • (1 : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ]
        EuclideanSpace ℂ (Fin 2)) := by
    ext v
    simp [complexSpectralPowerBlockCLM, complexScalarBlockCLM, w]
  rw [hmap, map_smul, LinearMap.trace_one]
  simp [complexSpectralTraceTerm, complexSpectralPowerWeight, w] <;> ring

end Neoplatonic.LTR
