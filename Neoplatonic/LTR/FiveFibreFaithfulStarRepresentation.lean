import Neoplatonic.LTR.FiveFibreAtomicConnesNoGo
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Tactic

/-!
# LTR-MAN-53: faithful unital star representations reduce to atomic resolutions

Given an injective unital complex star-algebra homomorphism from
the four-atom truth algebra ℂ^4 to the five-dimensional complex
matrix algebra, evaluate it on the four minimal atomic indicators.
Their images are four nonzero pairwise orthogonal Hermitian
idempotents summing to the identity.

MAN-52's arbitrary-atomic-representation Connes distance obstruction
then applies to the original representation, with the literal
represented observable rho(f) and the actual Hilbert operator norm.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev FiveMat := Matrix (Fin 5) (Fin 5) ℂ

/-- Characteristic function of one of the four truth atoms. -/
def fiveFibreTruthAtom (v : Fin 4) : Fin 4 → ℂ :=
  Pi.single v 1

theorem fiveFibreTruthAtom_star (v : Fin 4) :
    star (fiveFibreTruthAtom v) = fiveFibreTruthAtom v := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [fiveFibreTruthAtom]
  · simp [fiveFibreTruthAtom, Pi.single_apply, hw]

theorem fiveFibreTruthAtom_idempotent (v : Fin 4) :
    fiveFibreTruthAtom v * fiveFibreTruthAtom v =
      fiveFibreTruthAtom v := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [fiveFibreTruthAtom]
  · simp [fiveFibreTruthAtom, Pi.single_apply, hw]

theorem fiveFibreTruthAtom_orthogonal
    (v w : Fin 4) (hvw : v ≠ w) :
    fiveFibreTruthAtom v * fiveFibreTruthAtom w = 0 := by
  funext i
  by_cases hv : i = v
  · subst i
    simp [fiveFibreTruthAtom, Pi.single_apply, Ne.symm hvw]
  · simp [fiveFibreTruthAtom, Pi.single_apply, hv]

theorem fiveFibreTruthAtom_sum_one :
    (∑ v : Fin 4, fiveFibreTruthAtom v) = 1 := by
  funext w
  simp [fiveFibreTruthAtom, Pi.single_apply]

/-- Each truth profile is the sum of its four values multiplied
by the corresponding minimal atomic indicators. -/
theorem fiveFibreTruthAtom_sum_repr (f : Fin 4 → ℂ) :
    (∑ v : Fin 4, f v • fiveFibreTruthAtom v) = f := by
  funext w
  simp [fiveFibreTruthAtom, Pi.single_apply, smul_eq_mul]

/-- The four minimal truth indicators of any faithful unital star
representation give a faithful atomic orthogonal resolution of I₅. -/
noncomputable def fiveFibreAtomicResolution_of_starAlgHom
    (ρ : (Fin 4 → ℂ) →⋆ₐ[ℂ] FiveMat)
    (hρ : Function.Injective ρ) : FiveFibreAtomicResolution where
  proj v := ρ (fiveFibreTruthAtom v)
  hermitian v := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
    change star (ρ (fiveFibreTruthAtom v)) = ρ (fiveFibreTruthAtom v)
    rw [← map_star, fiveFibreTruthAtom_star]
  idempotent v := by
    change ρ (fiveFibreTruthAtom v) * ρ (fiveFibreTruthAtom v) =
      ρ (fiveFibreTruthAtom v)
    rw [← map_mul, fiveFibreTruthAtom_idempotent]
  orthogonal v w hvw := by
    change ρ (fiveFibreTruthAtom v) * ρ (fiveFibreTruthAtom w) = 0
    rw [← map_mul, fiveFibreTruthAtom_orthogonal v w hvw, map_zero]
  sum_one := by
    change (∑ v : Fin 4, ρ (fiveFibreTruthAtom v)) = 1
    rw [← map_sum, fiveFibreTruthAtom_sum_one, map_one]
  nonzero v := by
    intro hz
    have heq : fiveFibreTruthAtom v = (0 : Fin 4 → ℂ) := by
      apply hρ
      simpa using hz
    have hentry := congrArg (fun f : Fin 4 → ℂ => f v) heq
    norm_num [fiveFibreTruthAtom, Pi.single_apply] at hentry

/-- The literal star-algebra representation is exactly the sum
of its atomic projections weighted by the four truth values. -/
theorem fiveFibreStarRep_eq_atomicObservable
    (ρ : (Fin 4 → ℂ) →⋆ₐ[ℂ] FiveMat)
    (hρ : Function.Injective ρ)
    (f : Fin 4 → ℂ) :
    ρ f = (fiveFibreAtomicResolution_of_starAlgHom ρ hρ).representedObservable f := by
  calc
    ρ f = ρ (∑ v : Fin 4, f v • fiveFibreTruthAtom v) := by
      rw [fiveFibreTruthAtom_sum_repr]
    _ = ∑ v : Fin 4, f v • ρ (fiveFibreTruthAtom v) := by
      simp only [map_sum, map_smul]
    _ = (fiveFibreAtomicResolution_of_starAlgHom ρ hρ).representedObservable f := rfl

/-- Genuine bounded-Hilbert Dirac commutator of an arbitrary
unital complex star representation on five Hilbert coordinates. -/
noncomputable def fiveFibreStarRepDiracComm
    (ρ : (Fin 4 → ℂ) →⋆ₐ[ℂ] FiveMat)
    (D : FiveMat) (f : Fin 4 → ℂ) :
    EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5) :=
  (D * ρ f - ρ f * D).toEuclideanLin.toContinuousLinearMap

/-- The original represented commutator is the atomic
resolution commutator obtained from the four truth idempotents. -/
theorem fiveFibreStarRepDiracComm_eq_atomic
    (ρ : (Fin 4 → ℂ) →⋆ₐ[ℂ] FiveMat)
    (hρ : Function.Injective ρ)
    (D : FiveMat) (f : Fin 4 → ℂ) :
    fiveFibreStarRepDiracComm ρ D f =
      (fiveFibreAtomicResolution_of_starAlgHom ρ hρ).atomicDiracComm D f := by
  unfold fiveFibreStarRepDiracComm
    FiveFibreAtomicResolution.atomicDiracComm
  rw [← fiveFibreStarRep_eq_atomicObservable ρ hρ f]

def fiveFibreStarRepAdmissible
    (ρ : (Fin 4 → ℂ) →⋆ₐ[ℂ] FiveMat) (D : FiveMat) : Type :=
  { f : Fin 4 → ℂ // ‖fiveFibreStarRepDiracComm ρ D f‖ ≤ 1 }

/-- Extended-real Connes dual pseudodistance of the literal
faithful unital star-algebra representation on ℂ^5. -/
noncomputable def fiveFibreStarRepConnesDistance
    (ρ : (Fin 4 → ℂ) →⋆ₐ[ℂ] FiveMat)
    (D : FiveMat) (u w : Fin 4) : ℝ≥0∞ :=
  ⨆ f : fiveFibreStarRepAdmissible ρ D,
    (‖f.val u - f.val w‖₊ : ℝ≥0∞)

/-- Every faithful unital star representation has exactly the
same Connes dual pseudometric as its atomic resolution. -/
theorem fiveFibreStarRepConnesDistance_eq_atomic
    (ρ : (Fin 4 → ℂ) →⋆ₐ[ℂ] FiveMat)
    (hρ : Function.Injective ρ)
    (D : FiveMat) (u w : Fin 4) :
    fiveFibreStarRepConnesDistance ρ D u w =
      (fiveFibreAtomicResolution_of_starAlgHom ρ hρ).atomicConnesDistance D u w := by
  unfold fiveFibreStarRepConnesDistance
    FiveFibreAtomicResolution.atomicConnesDistance
  apply le_antisymm
  · apply iSup_le
    intro f
    have hunit :
        ‖(fiveFibreAtomicResolution_of_starAlgHom ρ hρ).atomicDiracComm
          D f.val‖ ≤ 1 := by
      rw [← fiveFibreStarRepDiracComm_eq_atomic ρ hρ D f.val]
      exact f.property
    let g : (fiveFibreAtomicResolution_of_starAlgHom ρ hρ).atomicAdmissible
        D := ⟨f.val, hunit⟩
    exact le_iSup
      (fun h : (fiveFibreAtomicResolution_of_starAlgHom ρ hρ).atomicAdmissible
        D => (‖h.val u - h.val w‖₊ : ℝ≥0∞)) g
  · apply iSup_le
    intro f
    have hunit : ‖fiveFibreStarRepDiracComm ρ D f.val‖ ≤ 1 := by
      rw [fiveFibreStarRepDiracComm_eq_atomic ρ hρ D f.val]
      exact f.property
    let g : fiveFibreStarRepAdmissible ρ D := ⟨f.val, hunit⟩
    exact le_iSup
      (fun h : fiveFibreStarRepAdmissible ρ D =>
        (‖h.val u - h.val w‖₊ : ℝ≥0∞)) g

/-- No faithful unital complex star representation of the two-bit
truth algebra on ℂ^5 has all exact Hamming Connes distances. -/
theorem fiveFibreFaithfulStarRep_exactHamming_noGo
    (ρ : (Fin 4 → ℂ) →⋆ₐ[ℂ] FiveMat)
    (hρ : Function.Injective ρ)
    (D : FiveMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u w : Fin 4,
      fiveFibreStarRepConnesDistance ρ D u w =
        (twoBitSquareHamming u w : ℝ≥0∞)) :
    False := by
  let P := fiveFibreAtomicResolution_of_starAlgHom ρ hρ
  apply P.exactHamming_noGo D hD
  intro u w
  rw [← fiveFibreStarRepConnesDistance_eq_atomic ρ hρ D u w]
  exact hham u w

end Neoplatonic.LTR
