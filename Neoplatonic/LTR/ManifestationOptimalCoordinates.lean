import Neoplatonic.LTR.ManifestationFiniteRankIsometry
import Mathlib.Data.Finset.Card

/-!
# LTR-MAN-08: select exactly one scalar observation per Boolean profile

The original syntax-numbered spectral triple chooses an infinite dense
sequence of completed theories. Each finite truth pattern occurs in it.
We choose the first occurrence and use the actual marked Dirac block
indexed by Nat.pair firstHit anchor.

Different truth patterns have different selected block indices.
The selected finite set has exactly 2^m members, and every one of
its marked LEFT endpoints realizes its associated m-bit assignment.

A diagonal sparse Hilbert cutoff keeps only the first scalar coordinate
of each selected block. This is a genuine bounded operator on the
original infinite complex Hilbert space, with contraction and
idempotence to be certified below.

All choices of complete theories come from the same classical dense
enumeration already used by the full spectral triple.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open scoped lp

/-- The selected marked block for an actual m-bit truth profile. -/
noncomputable def optimalManifestationBlock (m : ℕ)
    (bits : Fin m → Bool) : ℕ :=
  Nat.pair
    (manifestationPrefixFirstHit
      effectiveNullaryDenseSeq effectiveNullaryDenseSeq_dense m bits)
    effectiveNullaryDenseMarkA

/-- Its LEFT endpoint realizes the specified truth profile. -/
theorem optimalManifestationBlock_prefix (m : ℕ)
    (bits : Fin m → Bool) :
    manifestationPrefix m
      (effectiveNullaryMarkedLeft (optimalManifestationBlock m bits)) =
      bits := by
  unfold optimalManifestationBlock
  rw [effectiveNullaryMarkedLeft_pair_anchor]
  exact manifestationPrefixFirstHit_spec
    effectiveNullaryDenseSeq effectiveNullaryDenseSeq_dense m bits

/-- Different truth profiles require different selected block indices. -/
theorem optimalManifestationBlock_injective (m : ℕ) :
    Function.Injective (optimalManifestationBlock m) := by
  intro a b h
  calc
    a = manifestationPrefix m
        (effectiveNullaryMarkedLeft (optimalManifestationBlock m a)) :=
      (optimalManifestationBlock_prefix m a).symm
    _ = manifestationPrefix m
        (effectiveNullaryMarkedLeft (optimalManifestationBlock m b)) := by
      rw [h]
    _ = b := optimalManifestationBlock_prefix m b

/-- The set of all selected, pairwise distinct block indices. -/
noncomputable def optimalManifestationBlockSet (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.univ : Finset (Fin m → Bool)).image
    (optimalManifestationBlock m)

/-- Each specified pattern's block belongs to the selected support. -/
theorem optimalManifestationBlock_mem (m : ℕ) (bits : Fin m → Bool) :
    optimalManifestationBlock m bits ∈ optimalManifestationBlockSet m := by
  classical
  unfold optimalManifestationBlockSet
  exact Finset.mem_image.mpr ⟨bits, Finset.mem_univ _, rfl⟩

/-- The support has the EXACT capacity of the Boolean fragment. -/
theorem optimalManifestationBlockSet_card (m : ℕ) :
    (optimalManifestationBlockSet m).card = 2 ^ m := by
  classical
  unfold optimalManifestationBlockSet
  rw [Finset.card_image_of_injective _
    (optimalManifestationBlock_injective m)]
  simp [Fintype.card_fun]

/-- A one-coordinate cutoff using the actual two-point observable block
diag(1,0). Every omitted Hilbert block is sent to zero. -/
noncomputable def optimalManifestationHilbertProjection (m : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert := by
  classical
  exact lp.mapCLM 2
    (fun j => if j ∈ optimalManifestationBlockSet m
      then complexValuedObservableBlock 1 0
      else 0)
    (by norm_num : (0 : ℝ) ≤ 1)
    (by
      intro j
      by_cases hj : j ∈ optimalManifestationBlockSet m
      · simpa only [if_pos hj] using
          complexValuedObservableBlock_norm_le
            (1 : ℂ) 0 1 (by norm_num) (by norm_num) (by norm_num)
      · simpa only [if_neg hj, norm_zero] using
          (zero_le_one : (0 : ℝ) ≤ 1))

/-- Exact coordinate action of the rank-one-per-profile projection. -/
theorem optimalManifestationHilbertProjection_apply
    (m : ℕ) (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (optimalManifestationHilbertProjection m ψ) j =
      if j ∈ optimalManifestationBlockSet m
      then complexValuedObservableBlock 1 0 (ψ j)
      else 0 := by
  change (if j ∈ optimalManifestationBlockSet m
    then complexValuedObservableBlock 1 0
    else 0) (ψ j) = _
  by_cases hj : j ∈ optimalManifestationBlockSet m <;> simp [hj]

/-- The chosen Hilbert cutoff is a contraction. -/
theorem optimalManifestationHilbertProjection_norm_le_one (m : ℕ) :
    ‖optimalManifestationHilbertProjection m‖ ≤ 1 := by
  classical
  unfold optimalManifestationHilbertProjection
  apply lp.norm_mapCLM_le 2
    (fun j => if j ∈ optimalManifestationBlockSet m
      then complexValuedObservableBlock 1 0 else 0)
    (by norm_num : (0 : ℝ) ≤ 1)
  intro j
  by_cases hj : j ∈ optimalManifestationBlockSet m
  · simpa only [if_pos hj] using
      complexValuedObservableBlock_norm_le
        (1 : ℂ) 0 1 (by norm_num) (by norm_num) (by norm_num)
  · simpa only [if_neg hj, norm_zero] using
      (zero_le_one : (0 : ℝ) ≤ 1)

/-- The coordinate-0 Hilbert block is an algebraic projection. -/
theorem optimalManifestationLeftBlock_idempotent :
    (complexValuedObservableBlock 1 0).comp
      (complexValuedObservableBlock 1 0) =
      complexValuedObservableBlock 1 0 := by
  rw [complexValuedObservableBlock_mul]
  norm_num

/-- The rank-one-per-profile cutoff is idempotent. -/
theorem optimalManifestationHilbertProjection_idempotent (m : ℕ) :
    (optimalManifestationHilbertProjection m).comp
      (optimalManifestationHilbertProjection m) =
      optimalManifestationHilbertProjection m := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [ContinuousLinearMap.comp_apply,
    optimalManifestationHilbertProjection_apply,
    optimalManifestationHilbertProjection_apply]
  by_cases hj : j ∈ optimalManifestationBlockSet m
  · simp only [if_pos hj]
    change (complexValuedObservableBlock 1 0).comp
      (complexValuedObservableBlock 1 0) (ψ j) =
      complexValuedObservableBlock 1 0 (ψ j)
    rw [optimalManifestationLeftBlock_idempotent]
  · simp [hj]

end Neoplatonic.LTR.Nullary
