import Neoplatonic.LTR.WeightedDiracRange

/-!
# Two-sided infinite Hilbert-space squared-resolvent identities

On H = ℓ²(ℕ,ℝ²), let D be the maximal-domain direct sum of
  D_j = [[2^j, s_j], [s_j, -2^j]].
The bounded compact map R has weights
  w_j = (1 + 4^j + s_j²)⁻¹.

Uniform weighted-block estimates first show that Rψ is in Dom(D)
and that D(Rψ) is also in Dom(D), for every ψ ∈ H.
The finite-dimensional matrix identity is then applied coordinatewise
to prove

  Rψ + D(D(Rψ)) = ψ                      for all ψ ∈ H,
  R(ψ + D(Dψ)) = ψ                      for ψ ∈ Dom(D²).

These are the explicit two-sided inverse equations for I+D², with
the unbounded compositions only formed where the domain proofs exist.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The compact squared-resolvent candidate maps every ψ into the
domain of D², formulated as D(Rψ) ∈ Dom(D). -/
theorem chosenSquaredResolvent_D_mem_maximalDiracDomain
    (scale : ℕ → ℝ) (ψ : DiracBlockHilbert) :
    (maximalDiracPMap (fun j => (2 : ℝ) ^ j) scale)
      ⟨chosenSquaredResolventCLM scale ψ,
        chosenSquaredResolvent_mem_maximalDiracDomain scale ψ⟩ ∈
      maximalDiracDomain (fun j => (2 : ℝ) ^ j) scale := by
  change Memℓp
    (diracBlockwise (fun j => (2 : ℝ) ^ j) scale
      ((maximalDiracPMap (fun j => (2 : ℝ) ^ j) scale)
        ⟨chosenSquaredResolventCLM scale ψ,
          chosenSquaredResolvent_mem_maximalDiracDomain scale ψ⟩)) 2
  apply (lp.memℓp ψ).mono'
  intro j
  change ‖euclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
    (euclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      ((chosenSquaredResolventCLM scale ψ) j))‖ ≤ ‖ψ j‖
  rw [chosenSquaredResolventCLM_apply]
  exact weightedEuclideanDiracBlock_square_norm_le
    ((2 : ℝ) ^ j) (scale j) (ψ j)

/-- For every Hilbert vector, the compact squared-resolvent
candidate supplies a solution of (I+D²)x=ψ in the actual Dom(D²). -/
theorem chosenSquaredResolvent_right_inverse
    (scale : ℕ → ℝ) (ψ : DiracBlockHilbert) :
    chosenSquaredResolventCLM scale ψ +
      (maximalDiracPMap (fun j => (2 : ℝ) ^ j) scale)
        ⟨(maximalDiracPMap (fun j => (2 : ℝ) ^ j) scale)
          ⟨chosenSquaredResolventCLM scale ψ,
            chosenSquaredResolvent_mem_maximalDiracDomain scale ψ⟩,
          chosenSquaredResolvent_D_mem_maximalDiracDomain scale ψ⟩ = ψ := by
  apply lp.ext
  funext j
  change (chosenSquaredResolventCLM scale ψ) j +
    euclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      (euclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
        ((chosenSquaredResolventCLM scale ψ) j)) = ψ j
  rw [chosenSquaredResolventCLM_apply]
  exact squaredResolventWeight_block_inverse scale j (ψ j)

/-- Conversely R(I+D²) is the identity on the precise domain
where both unbounded applications of D are defined. -/
theorem chosenSquaredResolvent_left_inverse
    (scale : ℕ → ℝ) (ψ : DiracBlockHilbert)
    (hψ : ψ ∈ maximalDiracDomain (fun j => (2 : ℝ) ^ j) scale)
    (hDψ : (maximalDiracPMap (fun j => (2 : ℝ) ^ j) scale)
        ⟨ψ, hψ⟩ ∈ maximalDiracDomain (fun j => (2 : ℝ) ^ j) scale) :
    chosenSquaredResolventCLM scale
      (ψ + (maximalDiracPMap (fun j => (2 : ℝ) ^ j) scale)
        ⟨(maximalDiracPMap (fun j => (2 : ℝ) ^ j) scale)
          ⟨ψ, hψ⟩, hDψ⟩) = ψ := by
  apply lp.ext
  funext j
  rw [chosenSquaredResolventCLM_apply]
  change chosenSquaredResolventWeight scale j •
    (ψ j + euclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      (euclideanDiracBlock ((2 : ℝ) ^ j) (scale j) (ψ j))) = ψ j
  rw [euclideanDiracBlock_square, smul_add, smul_smul, ← add_smul,
    chosenSquaredResolventWeight_inverse, one_smul]

end Neoplatonic.LTR
