import Neoplatonic.LTR.FiveFibreAtomicConjugacy
import Mathlib.Tactic

/-!
# LTR-MAN-52: exact Hamming no-go for arbitrary faithful atomic truth representations

The four atomic projections determine a literal represented observable
rho(f) = sum_v f(v) P_v. MAN-51 proves that each P_v is the unitary
conjugate of its diagonal truth-indicator matrix. Linear extension
identifies rho(f) with the unitary conjugate of the faithful labelled
diagonal representation from MAN-45.

Thus the actual finite-dimensional Dirac commutator norm, the
extended-real Connes dual supremum and the exact Hamming obstruction
transport to every faithful atomic resolution of identity.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix

private abbrev FiveMat := Matrix (Fin 5) (Fin 5) ℂ

/-- The literal four-truth-value representation arising from four
Hermitian orthogonal atomic projections on five Hilbert coordinates. -/
noncomputable def FiveFibreAtomicResolution.representedObservable
    (P : FiveFibreAtomicResolution) (f : Fin 4 → ℂ) : FiveMat :=
  ∑ v : Fin 4, f v • P.proj v

/-- Weighted diagonal atom indicators sum to the labelled diagonal
observable, for all four complex truth values. -/
theorem FiveFibreAtomicResolution.sum_diagonalIndicators
    (P : FiveFibreAtomicResolution) (f : Fin 4 → ℂ) :
    (∑ v : Fin 4,
      f v • Matrix.diagonal (P.atomicIndicator v)) =
        Matrix.diagonal (fun j => f (P.atomicBasisLabel j)) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, atomicIndicator,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  · simp [Matrix.diagonal_apply, hij,
      Matrix.sum_apply, Matrix.smul_apply]

/-- Every represented truth observable is exactly the unitary
conjugate of a diagonal observable in the recovered faithful chart. -/
theorem FiveFibreAtomicResolution.representedObservable_eq_unitaryConj
    (P : FiveFibreAtomicResolution) (f : Fin 4 → ℂ) :
    P.representedObservable f =
      (fiveFibre_unitaryAut P.atomicBasisUnitary)
        (Matrix.diagonal (fun j => f (P.atomicBasisLabel j))) := by
  let A := fiveFibre_unitaryAut P.atomicBasisUnitary
  calc
    P.representedObservable f = ∑ v : Fin 4, f v • P.proj v := rfl
    _ = ∑ v : Fin 4, f v • A (Matrix.diagonal (P.atomicIndicator v)) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [P.atomicProjection_eq_unitaryConj v]
    _ = A (∑ v : Fin 4, f v • Matrix.diagonal (P.atomicIndicator v)) := by
      simp only [map_sum, map_smul]
    _ = A (Matrix.diagonal (fun j => f (P.atomicBasisLabel j))) := by
      rw [P.sum_diagonalIndicators]

/-- The literal Dirac commutator for the arbitrary atomic
four-truth representation, as a genuine bounded Hilbert operator. -/
noncomputable def FiveFibreAtomicResolution.atomicDiracComm
    (P : FiveFibreAtomicResolution) (D : FiveMat)
    (f : Fin 4 → ℂ) :
    EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5) :=
  (D * P.representedObservable f - P.representedObservable f * D
    ).toEuclideanLin.toContinuousLinearMap

/-- The represented atomic commutator equals the corresponding
unitary-conjugated diagonal commutator. -/
theorem FiveFibreAtomicResolution.atomicDiracComm_eq_conjugated
    (P : FiveFibreAtomicResolution) (D : FiveMat)
    (f : Fin 4 → ℂ) :
    P.atomicDiracComm D f =
      fiveFibreConjugatedDiracComm
        P.atomicBasisUnitary P.atomicBasisLabel D f := by
  unfold FiveFibreAtomicResolution.atomicDiracComm
    fiveFibreConjugatedDiracComm
  rw [P.representedObservable_eq_unitaryConj]
  rfl

/-- Complex four-truth observables in the actual Connes Dirac
commutator unit ball of an arbitrary faithful atomic resolution. -/
def FiveFibreAtomicResolution.atomicAdmissible
    (P : FiveFibreAtomicResolution) (D : FiveMat) : Type :=
  { f : Fin 4 → ℂ // ‖P.atomicDiracComm D f‖ ≤ 1 }

/-- Extended-real Connes dual pseudodistance of an arbitrary
faithful four-atom resolution on five Hilbert coordinates. -/
noncomputable def FiveFibreAtomicResolution.atomicConnesDistance
    (P : FiveFibreAtomicResolution) (D : FiveMat)
    (u w : Fin 4) : ℝ≥0∞ :=
  ⨆ f : P.atomicAdmissible D,
    (‖f.val u - f.val w‖₊ : ℝ≥0∞)

/-- The original atomic Connes metric equals the unitary-conjugated
labelled diagonal Connes metric for every truth-atom pair. -/
theorem FiveFibreAtomicResolution.atomicConnesDistance_eq_conjugated
    (P : FiveFibreAtomicResolution) (D : FiveMat)
    (u w : Fin 4) :
    P.atomicConnesDistance D u w =
      fiveFibreConjugatedConnesDistance
        P.atomicBasisUnitary P.atomicBasisLabel D u w := by
  unfold FiveFibreAtomicResolution.atomicConnesDistance
    fiveFibreConjugatedConnesDistance
  apply le_antisymm
  · apply iSup_le
    intro f
    have hunit :
        ‖fiveFibreConjugatedDiracComm
          P.atomicBasisUnitary P.atomicBasisLabel D f.val‖ ≤ 1 := by
      rw [← P.atomicDiracComm_eq_conjugated D f.val]
      exact f.property
    let g : fiveFibreConjugatedAdmissible
      P.atomicBasisUnitary P.atomicBasisLabel D := ⟨f.val, hunit⟩
    exact le_iSup
      (fun h : fiveFibreConjugatedAdmissible
        P.atomicBasisUnitary P.atomicBasisLabel D =>
          (‖h.val u - h.val w‖₊ : ℝ≥0∞)) g
  · apply iSup_le
    intro f
    have hunit : ‖P.atomicDiracComm D f.val‖ ≤ 1 := by
      rw [P.atomicDiracComm_eq_conjugated D f.val]
      exact f.property
    let g : P.atomicAdmissible D := ⟨f.val, hunit⟩
    exact le_iSup
      (fun h : P.atomicAdmissible D =>
        (‖h.val u - h.val w‖₊ : ℝ≥0∞)) g

/-- Exact Hamming Connes distances are impossible on any faithful
four-atom orthogonal resolution of identity in complex dimension five. -/
theorem FiveFibreAtomicResolution.exactHamming_noGo
    (P : FiveFibreAtomicResolution)
    (D : FiveMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u w : Fin 4,
      P.atomicConnesDistance D u w =
        (twoBitSquareHamming u w : ℝ≥0∞)) :
    False := by
  apply fiveFibreUnitaryFaithful_exactHamming_noGo
    P.atomicBasisUnitary P.atomicBasisLabel
    P.atomicBasisLabel_surjective D hD
  intro u w
  rw [← P.atomicConnesDistance_eq_conjugated D u w]
  exact hham u w

end Neoplatonic.LTR
