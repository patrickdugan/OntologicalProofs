import Neoplatonic.LTR.FiveFibreAttainerNormalization
import Mathlib.Tactic

/-!
# LTR-MAN-32: normalized opposite attainers force the two exact witnesses

The metric's four unit-edge bounds, when combined with normalized
opposite-corner distance-two attainers, force the canonical witness
vectors (0,1,1,2) and (1,0,2,1) by MAN-27 midpoint rigidity.

MAN-31 supplies the complex phase-and-translation normalization of
attaining admissible observables. This file identifies the
four-truth-vertex functions with their faithful five-dimensional
Hilbert-coordinate lifts, and derives actual unit-commutator
admissibility of the two canonical witnesses.

From here, MAN-30 produces both norm-one coordinate commutators.
The only extra existence premise is that each opposite dual-distance
supremum is attained by an admissible observable.
-/

namespace Neoplatonic.LTR

/-- Restrict a five-coordinate observable to its four atomic truth
values, using coordinates 0,1,2,3. -/
def fiveFibreSquareRestrict (f : Fin 5 → ℂ) (i : Fin 4) : ℂ :=
  f i.castSucc

/-- The faithful Hilbert lift recovers a represented observable
whose duplicate 00 coordinate agrees with its original one. -/
theorem fiveFibreSquareLift_restrict
    (f : Fin 5 → ℂ) (hf : f 4 = f 0) :
    fiveFibreSquareLift (fiveFibreSquareRestrict f) = f := by
  funext i
  fin_cases i <;>
    simp [fiveFibreSquareLift, fiveFibreSquareRestrict, hf]

/-- Four exact unit-edge Connes distances and attained norm-two
opposite-corner observables force both specific Hilbert-space
unit-commutator witnesses. -/
theorem fiveFibreSquare_attainedOpposites_force_witnesses
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hd01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (hd02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hd31 : fiveFibreSquareConnesDualDistance D 3 1 = 1)
    (hd32 : fiveFibreSquareConnesDualDistance D 3 2 = 1)
    (hatt03 : ∃ f : fiveFibreSquareAdmissible D,
      ‖f.val 3 - f.val 0‖ = 2)
    (hatt12 : ∃ f : fiveFibreSquareAdmissible D,
      ‖f.val 2 - f.val 1‖ = 2) :
    ‖fiveFibreSquareDiracComm D
      (fiveFibreSquareLift twoBitOppositeCornerSum)‖ ≤ 1 ∧
    ‖fiveFibreSquareDiracComm D
      (fiveFibreSquareLift twoBitOppositeCornerDifference)‖ ≤ 1 := by
  let L : (Fin 4 → ℂ) → ℝ := fun f =>
    ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f)‖
  have hupper : ∀ f : Fin 4 → ℂ, L f ≤ 1 →
      ‖f 0 - f 1‖ ≤ 1 ∧
      ‖f 0 - f 2‖ ≤ 1 ∧
      ‖f 3 - f 1‖ ≤ 1 ∧
      ‖f 3 - f 2‖ ≤ 1 := by
    intro f hf
    have hdup :
        fiveFibreSquareLift f 4 = fiveFibreSquareLift f 0 := by
      simp [fiveFibreSquareLift]
    have hu : ‖fiveFibreSquareDiracComm D
        (fiveFibreSquareLift f)‖ ≤ 1 := hf
    have h01 := fiveFibreSquareConnesDualDistance_bounds D 0 1 1
      (by simp [hd01]) (fiveFibreSquareLift f) hdup hu
    have h02 := fiveFibreSquareConnesDualDistance_bounds D 0 2 1
      (by simp [hd02]) (fiveFibreSquareLift f) hdup hu
    have h31 := fiveFibreSquareConnesDualDistance_bounds D 3 1 1
      (by simp [hd31]) (fiveFibreSquareLift f) hdup hu
    have h32 := fiveFibreSquareConnesDualDistance_bounds D 3 2 1
      (by simp [hd32]) (fiveFibreSquareLift f) hdup hu
    exact ⟨by simpa [fiveFibreSquareLift] using h01,
      by simpa [fiveFibreSquareLift] using h02,
      by simpa [fiveFibreSquareLift] using h31,
      by simpa [fiveFibreSquareLift] using h32⟩
  have hsum : ∃ f : Fin 4 → ℂ,
      L f ≤ 1 ∧ f 0 = 0 ∧ f 3 = 2 := by
    obtain ⟨g, hgdup, hgunit, hg0, hg3⟩ :=
      fiveFibreSquare_normalizeSubtypeAttainer D 0 3 hatt03
    refine ⟨fiveFibreSquareRestrict g, ?_, ?_, ?_⟩
    · change ‖fiveFibreSquareDiracComm D
          (fiveFibreSquareLift (fiveFibreSquareRestrict g))‖ ≤ 1
      rw [fiveFibreSquareLift_restrict g hgdup]
      exact hgunit
    · simpa [fiveFibreSquareRestrict] using hg0
    · simpa [fiveFibreSquareRestrict] using hg3
  have hdiff : ∃ f : Fin 4 → ℂ,
      L f ≤ 1 ∧ f 1 = 0 ∧ f 2 = 2 := by
    obtain ⟨g, hgdup, hgunit, hg1, hg2⟩ :=
      fiveFibreSquare_normalizeSubtypeAttainer D 1 2 hatt12
    refine ⟨fiveFibreSquareRestrict g, ?_, ?_, ?_⟩
    · change ‖fiveFibreSquareDiracComm D
          (fiveFibreSquareLift (fiveFibreSquareRestrict g))‖ ≤ 1
      rw [fiveFibreSquareLift_restrict g hgdup]
      exact hgunit
    · simpa [fiveFibreSquareRestrict] using hg1
    · simpa [fiveFibreSquareRestrict] using hg2
  exact twoBitOppositeAttainers_force_coordinateWitnesses
    L hupper hsum hdiff

/-- Six exact finite Hamming distances and attainment of the two
opposite-corner suprema force the two direction commutators to have
the exact norm one required by the graded spectral theorem. -/
theorem fiveFibreSquare_attainedHamming_normOne
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hd01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (hd02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hd31 : fiveFibreSquareConnesDualDistance D 3 1 = 1)
    (hd32 : fiveFibreSquareConnesDualDistance D 3 2 = 1)
    (hatt03 : ∃ f : fiveFibreSquareAdmissible D,
      ‖f.val 3 - f.val 0‖ = 2)
    (hatt12 : ∃ f : fiveFibreSquareAdmissible D,
      ‖f.val 2 - f.val 1‖ = 2) :
    ‖(fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap‖ = 1 ∧
    ‖(fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap‖ = 1 := by
  obtain ⟨hsum, hdiff⟩ :=
    fiveFibreSquare_attainedOpposites_force_witnesses
      D hd01 hd02 hd31 hd32 hatt03 hatt12
  exact fiveFibreSquare_exactEdgeDistance_normOne
    D hd01 hd02 hsum hdiff

end Neoplatonic.LTR
