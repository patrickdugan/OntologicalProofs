import Neoplatonic.LTR.ComplexWeightedDiracRange

/-!
# Exact (I + D_C²) inverse on the infinite complex Hilbert space

On ℓ²(ℕ,ℂ²) with the self-adjoint maximal-domain complex Dirac
operator D_C, the compact bounded operator R_C has weights
 w_j = (1+4^j+s_j²)⁻¹.
Uniform block estimates prove R_C(H) ⊆ Dom(D_C²).
Exact coordinate equations then prove both inverse identities.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The complex inverse-weight scalar identity, inherited from the
exact real rational identity under the natural scalar embedding. -/
theorem chosenComplexSquaredResolventWeight_inverse
    (scale : ℕ → ℝ) (j : ℕ) :
    ((chosenSquaredResolventWeight scale j : ℝ) : ℂ) +
      ((chosenSquaredResolventWeight scale j : ℝ) : ℂ) *
      (((((2 : ℝ) ^ j) ^ 2 + (scale j) ^ 2 : ℝ)) : ℂ) = 1 := by
  exact_mod_cast chosenSquaredResolventWeight_inverse scale j

/-- The complex block's chosen squared-resolvent weight solves
(I+D_j²)R_j=I on every Euclidean vector. -/
theorem complexSquaredResolventWeight_block_inverse
    (scale : ℕ → ℝ) (j : ℕ)
    (v : EuclideanSpace ℂ (Fin 2)) :
    (((chosenSquaredResolventWeight scale j : ℝ) : ℂ)) • v +
      complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
        (complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
          (((chosenSquaredResolventWeight scale j : ℝ) : ℂ)) • v) = v := by
  calc
    _ = (((chosenSquaredResolventWeight scale j : ℝ) : ℂ)) • v +
        (((chosenSquaredResolventWeight scale j : ℝ) : ℂ)) •
          (complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
            (complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j) v)) := by
              simp only [map_smul]
    _ = (((chosenSquaredResolventWeight scale j : ℝ) : ℂ)) • v +
        (((chosenSquaredResolventWeight scale j : ℝ) : ℂ)) •
          (((((2 : ℝ) ^ j) ^ 2 + (scale j) ^ 2 : ℝ) : ℂ) • v) := by
            rw [complexEuclideanDiracBlock_square]
    _ = v := by
      rw [smul_smul, ← add_smul,
        chosenComplexSquaredResolventWeight_inverse, one_smul]

/-- The compact complex squared resolvent maps all vectors into Dom(D_C²). -/
theorem chosenComplexSquaredResolvent_D_mem_maximalComplexDiracDomain
    (scale : ℕ → ℝ) (ψ : ComplexDiracBlockHilbert) :
    (maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale)
      ⟨chosenComplexSquaredResolventCLM scale ψ,
        chosenComplexSquaredResolvent_mem_maximalComplexDiracDomain scale ψ⟩ ∈
      maximalComplexDiracDomain (fun j => (2 : ℝ) ^ j) scale := by
  change Memℓp
    (complexDiracBlockwise (fun j => (2 : ℝ) ^ j) scale
      ((maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale)
        ⟨chosenComplexSquaredResolventCLM scale ψ,
          chosenComplexSquaredResolvent_mem_maximalComplexDiracDomain scale ψ⟩)) 2
  apply (lp.memℓp ψ).mono'
  intro j
  change ‖complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
    (complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      ((chosenComplexSquaredResolventCLM scale ψ) j))‖ ≤ ‖ψ j‖
  rw [chosenComplexSquaredResolventCLM_apply]
  exact weightedComplexEuclideanDiracBlock_square_norm_le
    ((2 : ℝ) ^ j) (scale j) (ψ j)

/-- The compact complex R is a right inverse of I+D_C² on H_C. -/
theorem chosenComplexSquaredResolvent_right_inverse
    (scale : ℕ → ℝ) (ψ : ComplexDiracBlockHilbert) :
    chosenComplexSquaredResolventCLM scale ψ +
      (maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale)
        ⟨(maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale)
          ⟨chosenComplexSquaredResolventCLM scale ψ,
            chosenComplexSquaredResolvent_mem_maximalComplexDiracDomain scale ψ⟩,
          chosenComplexSquaredResolvent_D_mem_maximalComplexDiracDomain scale ψ⟩ = ψ := by
  apply lp.ext
  funext j
  change (chosenComplexSquaredResolventCLM scale ψ) j +
    complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      (complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
        ((chosenComplexSquaredResolventCLM scale ψ) j)) = ψ j
  rw [chosenComplexSquaredResolventCLM_apply]
  exact complexSquaredResolventWeight_block_inverse scale j (ψ j)

/-- R(I+D_C²)=I on the domain of the twice-applied complex D_C. -/
theorem chosenComplexSquaredResolvent_left_inverse
    (scale : ℕ → ℝ) (ψ : ComplexDiracBlockHilbert)
    (hψ : ψ ∈ maximalComplexDiracDomain (fun j => (2 : ℝ) ^ j) scale)
    (hDψ : (maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale)
        ⟨ψ, hψ⟩ ∈ maximalComplexDiracDomain (fun j => (2 : ℝ) ^ j) scale) :
    chosenComplexSquaredResolventCLM scale
      (ψ + (maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale)
        ⟨(maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale)
          ⟨ψ, hψ⟩, hDψ⟩) = ψ := by
  apply lp.ext
  funext j
  rw [chosenComplexSquaredResolventCLM_apply]
  change ((chosenSquaredResolventWeight scale j : ℝ) : ℂ) •
    (ψ j + complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      (complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j) (ψ j))) = ψ j
  rw [complexEuclideanDiracBlock_square, smul_add, smul_smul, ← add_smul,
    chosenComplexSquaredResolventWeight_inverse, one_smul]

end Neoplatonic.LTR
