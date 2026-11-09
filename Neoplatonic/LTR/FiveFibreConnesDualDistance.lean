import Neoplatonic.LTR.FiveFibreAdjacentNorms
import Mathlib.Tactic

/-!
# LTR-MAN-30: actual Connes dual distance implies edge and diagonal bounds

For the canonical faithful five-dimensional representation, define the
Connes dual distance as an extended nonnegative real supremum over the
actual complex-valued observables on four truth vertices. Coordinates
0 and 4 must agree because they represent the same truth vertex.
The commutator norm is the genuine continuous Hilbert operator norm.

The extended-real codomain allows the distance to be infinite. If it
is finite, its defining supremum gives a bound for every admissible
observable. Exact Hamming unit-edge distances imply MAN-29's dual
edge inequalities. The exact opposite-corner distance supplies the
MAN-25 dual upper bound directly.

This removes the separate universally quantified dual-bound
premises from those theorems, and leaves normalized opposite-witness
attainment and the general faithful-representation basis reduction
as subsequent mathematical steps.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

/-- The admissible part of the four-truth-vertex observable space, in
the five-dimensional faithful Hilbert-coordinate representation. -/
def fiveFibreSquareAdmissible (D : Matrix (Fin 5) (Fin 5) ℂ) : Type :=
  { f : Fin 5 → ℂ //
    f 4 = f 0 ∧ ‖fiveFibreSquareDiracComm D f‖ ≤ 1 }

/-- Genuine Connes dual pseudodistance, taking values in [0,∞].
Both complex coordinate values and the actual Dirac commutator norm
are used. The fibre constraint keeps the represented algebra
four-dimensional despite the duplicated Hilbert coordinate. -/
noncomputable def fiveFibreSquareConnesDualDistance
    (D : Matrix (Fin 5) (Fin 5) ℂ) (u v : Fin 5) : ℝ≥0∞ :=
  ⨆ f : fiveFibreSquareAdmissible D,
    (‖f.val u - f.val v‖₊ : ℝ≥0∞)

/-- Any admissible observable has its value difference bounded by
the Connes dual distance defined as an extended-real supremum. -/
theorem fiveFibreSquareConnesDualDistance_bounds
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (u v : Fin 5) (r : ℝ≥0)
    (hD : fiveFibreSquareConnesDualDistance D u v ≤ (r : ℝ≥0∞))
    (f : Fin 5 → ℂ)
    (hf : f 4 = f 0)
    (hunit : ‖fiveFibreSquareDiracComm D f‖ ≤ 1) :
    ‖f u - f v‖ ≤ (r : ℝ) := by
  have hle :
      (‖f u - f v‖₊ : ℝ≥0∞) ≤
        fiveFibreSquareConnesDualDistance D u v := by
    unfold fiveFibreSquareConnesDualDistance
    exact le_iSup
      (fun g : fiveFibreSquareAdmissible D =>
        (‖g.val u - g.val v‖₊ : ℝ≥0∞))
      (⟨f, ⟨hf, hunit⟩⟩ : fiveFibreSquareAdmissible D)
  have hnn : ‖f u - f v‖₊ ≤ r :=
    ENNReal.coe_le_coe.mp (hle.trans hD)
  have hreal : (‖f u - f v‖₊ : ℝ) ≤ (r : ℝ) :=
    NNReal.coe_le_coe.mpr hnn
  simpa only [coe_nnnorm] using hreal

/-- When the actual dual pseudodistances of the 00--01 and 00--10
edges equal one, and both opposite-corner observables are admissible,
the coordinate Hermitian commutators have norm exactly one. -/
theorem fiveFibreSquare_exactEdgeDistance_normOne
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (h01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (h02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hsum :
      ‖fiveFibreSquareDiracComm D
        (fiveFibreSquareLift twoBitOppositeCornerSum)‖ ≤ 1)
    (hdiff :
      ‖fiveFibreSquareDiracComm D
        (fiveFibreSquareLift twoBitOppositeCornerDifference)‖ ≤ 1) :
    ‖(fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap‖ = 1 ∧
    ‖(fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap‖ = 1 := by
  apply fiveFibreSquare_adjacentDual_normOne D
  · intro f hf hunit
    exact fiveFibreSquareConnesDualDistance_bounds D 0 1 1
      (by simp [h01]) f hf hunit
  · intro f hf hunit
    exact fiveFibreSquareConnesDualDistance_bounds D 0 2 1
      (by simp [h02]) f hf hunit
  · exact hsum
  · exact hdiff

/-- The precise distance d(00,11)=2 supplies the dual bound
appearing as a hypothesis in MAN-25. -/
theorem fiveFibreSquare_exactOppositeDistance_dualBound
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (h03 : fiveFibreSquareConnesDualDistance D 0 3 = 2)
    (f : Fin 5 → ℂ)
    (hf : f 4 = f 0)
    (hunit : ‖fiveFibreSquareDiracComm D f‖ ≤ 1) :
    ‖f 0 - f 3‖ ≤ 2 :=
  fiveFibreSquareConnesDualDistance_bounds D 0 3 2
    (by simp [h03]) f hf hunit

/-- The isolated-truth-fibre contradiction uses the actual
Connes dual metric directly, eliminating the old abstract
kernel-constancy or universal dual-bound hypotheses. -/
theorem fiveFibreSquare_exactOppositeDistance_noGo
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0)
    (hA : fiveFibreSquareA D ≠ 0)
    (hB : fiveFibreSquareB D ≠ 0)
    (h03 : fiveFibreSquareConnesDualDistance D 0 3 = 2) :
    False := by
  apply fiveFibreSquare_connesDual_hamming_noGo
    D hD hAB hBA hA hB
  intro f hf hunit
  exact fiveFibreSquare_exactOppositeDistance_dualBound
    D h03 f hf (by simpa only [fiveFibreSquareDiracComm] using hunit)

end Neoplatonic.LTR
