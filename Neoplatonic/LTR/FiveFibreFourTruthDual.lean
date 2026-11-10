import Neoplatonic.LTR.FiveFibreFaithfulLabels
import Mathlib.Tactic

/-!
# LTR-MAN-42: Connes dual supremum indexed by four truth values

The canonical faithful five-coordinate representation has four
independent complex truth values: its fifth Hilbert coordinate is
another copy of the first. The original Connes dual distance of
MAN-30 takes a supremum over admissible five-coordinate functions
with that equality constraint.

The present construction takes the equivalent supremum directly over
four independent truth observables. An inadmissible observable
contributes zero to this extended nonnegative real supremum.
The lift/restrict equivalence of MAN-32 proves these two definitions
agree exactly on the four atomic truth vertices.

This reformulation makes a future change of truth labels and
Hilbert-coordinate permutation transparent: both transform the
same four-dimensional observable space.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

/-- Connes dual supremum on the four actual truth profiles, with
admissibility given by the genuine five-dimensional Dirac Hilbert
operator commutator norm. -/
noncomputable def fiveFibreFourTruthDualDistance
    (D : Matrix (Fin 5) (Fin 5) ℂ) (u v : Fin 4) : ℝ≥0∞ :=
  ⨆ f : Fin 4 → ℂ,
    if ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f)‖ ≤ 1 then
      (‖f u - f v‖₊ : ℝ≥0∞)
    else 0

/-- The direct four-observable supremum equals the original
five-coordinate Connes distance, which quantifies over actual
admissible represented five-coordinate observables. -/
theorem fiveFibreFourTruthDualDistance_eq_connes
    (D : Matrix (Fin 5) (Fin 5) ℂ) (u v : Fin 4) :
    fiveFibreFourTruthDualDistance D u v =
      fiveFibreSquareConnesDualDistance D u.castSucc v.castSucc := by
  apply le_antisymm
  · unfold fiveFibreFourTruthDualDistance
    apply iSup_le
    intro f
    by_cases hu :
        ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f)‖ ≤ 1
    · simp only [if_pos hu]
      have hdup : fiveFibreSquareLift f 4 = fiveFibreSquareLift f 0 := by
        simp [fiveFibreSquareLift]
      let g : fiveFibreSquareAdmissible D :=
        ⟨fiveFibreSquareLift f, ⟨hdup, hu⟩⟩
      have h :
          (‖g.val u.castSucc - g.val v.castSucc‖₊ : ℝ≥0∞) ≤
            fiveFibreSquareConnesDualDistance D u.castSucc v.castSucc := by
        unfold fiveFibreSquareConnesDualDistance
        exact le_iSup
          (fun a : fiveFibreSquareAdmissible D =>
            (‖a.val u.castSucc - a.val v.castSucc‖₊ : ℝ≥0∞))
          g
      simpa only [g, fiveFibreSquareLift_castSucc] using h
    · simp only [if_neg hu]
      exact bot_le
  · unfold fiveFibreSquareConnesDualDistance
    apply iSup_le
    intro g
    let f : Fin 4 → ℂ := fiveFibreSquareRestrict g.val
    have hlift : fiveFibreSquareLift f = g.val :=
      fiveFibreSquareLift_restrict g.val g.property.1
    have hu : ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f)‖ ≤ 1 := by
      rw [hlift]
      exact g.property.2
    have h :
        (‖f u - f v‖₊ : ℝ≥0∞) ≤ fiveFibreFourTruthDualDistance D u v := by
      unfold fiveFibreFourTruthDualDistance
      have hle := le_iSup
        (fun a : Fin 4 → ℂ =>
          if ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift a)‖ ≤ 1 then
            (‖a u - a v‖₊ : ℝ≥0∞)
          else 0) f
      simpa only [if_pos hu] using hle
    simpa only [f, fiveFibreSquareRestrict] using h

end Neoplatonic.LTR
