import Neoplatonic.LTR.ManifestationOptimalRank

/-!
# LTR-MAN-08D: identify the exact range of the sparse Hilbert projection

A selected two-point block acts as diag(1,0), hence keeps one
complex scalar coordinate. The whole projector has finite support,
with one selected marked block for each m-bit truth profile.

Its range equals the span of the selected orthonormal family
from MAN-08C. Consequently the rank of the *actual infinite-Hilbert
bounded operator* is precisely 2^m.

This range identity is the missing bridge between a coordinate
counting argument and an honest operator-rank theorem.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open scoped lp

/-- The first-coordinate block is a rank-one scalar projection
on the genuine two-dimensional Euclidean Hilbert space. -/
theorem optimalManifestationLeftBlock_apply
    (v : EuclideanSpace ℂ (Fin 2)) :
    complexValuedObservableBlock 1 0 v =
      (v 0) • EuclideanSpace.single (0 : Fin 2) (1 : ℂ) := by
  apply PiLp.ext
  intro k
  have hv := congrArg (fun h : Fin 2 → ℂ => h k)
    (Matrix.ofLp_toEuclideanCLM
      (complexValuedObservableMatrix (1 : ℂ) 0) v)
  change (complexValuedObservableBlock 1 0 v) k =
    (Matrix.mulVec (complexValuedObservableMatrix (1 : ℂ) 0)
      (fun i : Fin 2 => v i)) k at hv
  rw [hv, complexValuedObservableMatrix_diagonal,
    Matrix.mulVec_diagonal]
  fin_cases k <;> simp [PiLp.smul_apply, PiLp.single_apply]

/-- The sparse projection of a vector is a finite sum over its
selected blocks, using the actual Hilbert-coordinate insertion. -/
theorem optimalManifestationHilbertProjection_eq_sum
    (m : ℕ) (ψ : ComplexDiracBlockHilbert) :
    optimalManifestationHilbertProjection m ψ =
      ∑ j ∈ optimalManifestationBlockSet m,
        lp.single 2 j (complexValuedObservableBlock 1 0 (ψ j)) := by
  classical
  apply lp.ext
  funext j
  rw [optimalManifestationHilbertProjection_apply]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  simp [Finset.sum_pi_single]

/-- The chosen projection fixes each selected scalar basis vector. -/
theorem optimalManifestationHilbertProjection_fixes_basis
    (m : ℕ) (bits : Fin m → Bool) :
    optimalManifestationHilbertProjection m
      (optimalManifestationBasisVector m bits) =
        optimalManifestationBasisVector m bits := by
  classical
  apply lp.ext
  funext j
  rw [optimalManifestationHilbertProjection_apply]
  by_cases hj : j = optimalManifestationBlock m bits
  · subst j
    have hv : optimalManifestationBasisVector m bits
        (optimalManifestationBlock m bits) =
        EuclideanSpace.single (0 : Fin 2) (1 : ℂ) := by
      simp [optimalManifestationBasisVector, lp.single_apply_self]
    simp only [if_pos (optimalManifestationBlock_mem m bits)]
    rw [hv, optimalManifestationLeftBlock_apply]
    simp [hv, PiLp.single_apply]
  · have hz : optimalManifestationBasisVector m bits j = 0 := by
      unfold optimalManifestationBasisVector
      exact lp.single_apply_ne
        (E := fun _ : ℕ => EuclideanSpace ℂ (Fin 2))
        (2 : ENNReal) (optimalManifestationBlock m bits)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) hj
    by_cases hm : j ∈ optimalManifestationBlockSet m
    · simp [hm, hz]
    · simp [hm, hz]

/-- Every projected vector belongs to the finite span of
the 2^m chosen orthonormal Hilbert coordinate vectors. -/
theorem optimalManifestationHilbertProjection_mem_span
    (m : ℕ) (ψ : ComplexDiracBlockHilbert) :
    optimalManifestationHilbertProjection m ψ ∈
      optimalManifestationCoordinateSpace m := by
  classical
  rw [optimalManifestationHilbertProjection_eq_sum]
  apply Submodule.sum_mem
  intro j hj
  obtain ⟨bits, _, hbits⟩ :=
    Finset.mem_image.mp (show j ∈
      (Finset.univ : Finset (Fin m → Bool)).image
        (optimalManifestationBlock m) from
      (show j ∈ optimalManifestationBlockSet m from hj))
  subst j
  rw [optimalManifestationLeftBlock_apply, lp.single_smul]
  change ((ψ (optimalManifestationBlock m bits)) 0) •
    optimalManifestationBasisVector m bits ∈
      optimalManifestationCoordinateSpace m
  apply Submodule.smul_mem
  exact Submodule.subset_span
    (show optimalManifestationBasisVector m bits ∈
      Set.range (optimalManifestationBasisVector m) from
      ⟨bits, rfl⟩)

/-- Range of the actual sparse Hilbert operator is exactly the
rank-2^m profile-coordinate subspace. -/
theorem optimalManifestationHilbertProjection_range_eq_span
    (m : ℕ) :
    LinearMap.range (optimalManifestationHilbertProjection m).toLinearMap =
      optimalManifestationCoordinateSpace m := by
  apply le_antisymm
  · rintro v ⟨ψ, rfl⟩
    exact optimalManifestationHilbertProjection_mem_span m ψ
  · apply Submodule.span_le.mpr
    rintro v ⟨bits, rfl⟩
    refine ⟨optimalManifestationBasisVector m bits, ?_⟩
    exact optimalManifestationHilbertProjection_fixes_basis m bits

/-- Exact rank of the genuine scalar-coordinate Hilbert projector,
with the minimal one-dimensional realization of every m-bit profile. -/
theorem optimalManifestationHilbertProjection_rank_exact (m : ℕ) :
    Module.finrank ℂ
      (LinearMap.range
        (optimalManifestationHilbertProjection m).toLinearMap) =
      2 ^ m := by
  rw [optimalManifestationHilbertProjection_range_eq_span]
  exact optimalManifestationCoordinateSpace_finrank m

end Neoplatonic.LTR.Nullary
