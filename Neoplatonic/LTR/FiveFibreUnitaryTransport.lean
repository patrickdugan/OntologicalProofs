import Neoplatonic.LTR.FiveFibreFaithfulDiagonalNoGo
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Tactic

/-!
# LTR-MAN-46: unitary covariance of the actual Connes dual metric

The diagonal truth representation on ℂ^5 can be conjugated by any
unitary five-by-five complex matrix. Its represented observables,
Dirac matrix and their commutator transform together by a star-algebra
automorphism. The matrix C*-norm is the genuine continuous Hilbert
operator norm, so the entire extended-real Connes dual metric is
preserved.

This proves the exact Hamming obstruction for every unitary conjugate
of a faithful diagonal truth representation. The separate simultaneous
diagonalization obligation is to show that any faithful unital
star-representation of ℂ^4 on ℂ^5 is of that form.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev FiveMat := Matrix (Fin 5) (Fin 5) ℂ

/-- The conjugation star-algebra automorphism associated with
a unitary change of Hilbert basis. -/
def fiveFibre_unitaryAut (U : unitary FiveMat) :
    FiveMat ≃⋆ₐ[ℂ] FiveMat :=
  (Unitary.conjStarAlgAut ℂ FiveMat) U

/-- Unitary conjugation preserves the genuine complex Hilbert
operator norm of every five-by-five matrix. -/
theorem fiveFibre_unitaryAut_operatorNorm
    (U : unitary FiveMat) (M : FiveMat) :
    ‖((fiveFibre_unitaryAut U) M).toEuclideanLin.toContinuousLinearMap‖ =
      ‖M.toEuclideanLin.toContinuousLinearMap‖ := by
  have h := StarAlgEquiv.norm_map (fiveFibre_unitaryAut U) M
  simpa only [Matrix.l2_opNorm_def] using h

/-- Dirac commutator with the represented four-atom observable
after a unitary change of Hilbert basis. -/
noncomputable def fiveFibreConjugatedDiracComm
    (U : unitary FiveMat)
    (label : Fin 5 → Fin 4)
    (D : FiveMat) (f : Fin 4 → ℂ) :
    EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5) :=
  (D * (fiveFibre_unitaryAut U)
      (Matrix.diagonal (fun i => f (label i))) -
    (fiveFibre_unitaryAut U)
      (Matrix.diagonal (fun i => f (label i))) * D
    ).toEuclideanLin.toContinuousLinearMap

/-- The actual commutator norm is unchanged when the Dirac operator
and its represented truth algebra are conjugated together. -/
theorem fiveFibreConjugatedDiracComm_norm
    (U : unitary FiveMat)
    (label : Fin 5 → Fin 4)
    (D : FiveMat) (f : Fin 4 → ℂ) :
    ‖fiveFibreConjugatedDiracComm U label
      ((fiveFibre_unitaryAut U) D) f‖ =
    ‖fiveFibreLabelledDiracComm label D f‖ := by
  let A := fiveFibre_unitaryAut U
  let F : FiveMat := Matrix.diagonal (fun i => f (label i))
  have hcomm : A D * A F - A F * A D = A (D * F - F * D) := by
    simp only [map_sub, map_mul]
  have hnorm := fiveFibre_unitaryAut_operatorNorm U (D * F - F * D)
  unfold fiveFibreConjugatedDiracComm
    fiveFibreLabelledDiracComm fiveFibreSquareDiracComm
  change ‖(A D * A F - A F * A D).toEuclideanLin.toContinuousLinearMap‖ =
    ‖(D * F - F * D).toEuclideanLin.toContinuousLinearMap‖
  rw [hcomm]
  exact hnorm

/-- Four-truth observables admissible under the actual Dirac
commutator seminorm in a unitary-conjugated representation. -/
def fiveFibreConjugatedAdmissible
    (U : unitary FiveMat)
    (label : Fin 5 → Fin 4)
    (D : FiveMat) : Type :=
  { f : Fin 4 → ℂ // ‖fiveFibreConjugatedDiracComm U label D f‖ ≤ 1 }

/-- Extended-real Connes dual distance for any unitary conjugate
of a five-coordinate labelled diagonal truth representation. -/
noncomputable def fiveFibreConjugatedConnesDistance
    (U : unitary FiveMat)
    (label : Fin 5 → Fin 4)
    (D : FiveMat) (u v : Fin 4) : ℝ≥0∞ :=
  ⨆ f : fiveFibreConjugatedAdmissible U label D,
    (‖f.val u - f.val v‖₊ : ℝ≥0∞)

/-- Unitary conjugation preserves the entire Connes dual distance,
including the possibility of infinite values. -/
theorem fiveFibreConjugatedConnesDistance_eq_labelled
    (U : unitary FiveMat)
    (label : Fin 5 → Fin 4)
    (D : FiveMat) (u v : Fin 4) :
    fiveFibreConjugatedConnesDistance U label
      ((fiveFibre_unitaryAut U) D) u v =
    fiveFibreLabelledConnesDistance label D u v := by
  unfold fiveFibreConjugatedConnesDistance
    fiveFibreLabelledConnesDistance
  apply le_antisymm
  · apply iSup_le
    intro f
    have hnorm := fiveFibreConjugatedDiracComm_norm U label D f.val
    have hunit : ‖fiveFibreLabelledDiracComm label D f.val‖ ≤ 1 := by
      rw [← hnorm]
      exact f.property
    let g : fiveFibreLabelledAdmissible label D := ⟨f.val, hunit⟩
    exact le_iSup
      (fun h : fiveFibreLabelledAdmissible label D =>
        (‖h.val u - h.val v‖₊ : ℝ≥0∞)) g
  · apply iSup_le
    intro f
    have hnorm := fiveFibreConjugatedDiracComm_norm U label D f.val
    have hunit : ‖fiveFibreConjugatedDiracComm U label
        ((fiveFibre_unitaryAut U) D) f.val‖ ≤ 1 := by
      rw [hnorm]
      exact f.property
    let g : fiveFibreConjugatedAdmissible U label
        ((fiveFibre_unitaryAut U) D) := ⟨f.val, hunit⟩
    exact le_iSup
      (fun h : fiveFibreConjugatedAdmissible U label
          ((fiveFibre_unitaryAut U) D) =>
        (‖h.val u - h.val v‖₊ : ℝ≥0∞)) g

/-- Hermiticity of the Dirac matrix is preserved by a unitary
change of Hilbert basis. -/
theorem fiveFibre_unitaryAut_hermitian
    (U : unitary FiveMat)
    (D : FiveMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    ∀ i j, ((fiveFibre_unitaryAut U) D) i j =
      star (((fiveFibre_unitaryAut U) D) j i) := by
  have hDself : IsSelfAdjoint D :=
    (Matrix.IsHermitian.ext fun i j => (hD i j).symm).isSelfAdjoint
  have hMself : IsSelfAdjoint ((fiveFibre_unitaryAut U) D) := by
    change star ((fiveFibre_unitaryAut U) D) =
      (fiveFibre_unitaryAut U) D
    rw [← map_star, hDself.star_eq]
  have hM : ((fiveFibre_unitaryAut U) D).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr hMself
  intro i j
  exact (hM i j).symm

/-- Every unitary change of Hilbert basis of a faithful diagonal
representation is subject to the five-dimensional exact Hamming
Connes distance obstruction. -/
theorem fiveFibreUnitaryFaithful_exactHamming_noGo
    (U : unitary FiveMat)
    (label : Fin 5 → Fin 4)
    (hsurj : Function.Surjective label)
    (D : FiveMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      fiveFibreConjugatedConnesDistance U label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    False := by
  let A := fiveFibre_unitaryAut U
  let D' : FiveMat := A.symm D
  have hD' : ∀ i j, D' i j = star (D' j i) := by
    have h := fiveFibre_unitaryAut_hermitian (star U) D hD
    simpa only [D', A, fiveFibre_unitaryAut,
      Unitary.conjStarAlgAut_symm] using h
  apply fiveFibreFaithfulDiagonal_exactHamming_noGo label hsurj D' hD'
  intro u v
  have hnorm := fiveFibreConjugatedConnesDistance_eq_labelled U label D' u v
  have hback : A D' = D := A.apply_symm_apply D
  rw [hback] at hnorm
  exact hnorm.symm.trans (hham u v)

end Neoplatonic.LTR
