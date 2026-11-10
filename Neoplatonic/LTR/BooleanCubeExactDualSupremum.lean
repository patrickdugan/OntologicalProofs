import Neoplatonic.LTR.BooleanCubeConnesDistance
import Neoplatonic.LTR.BooleanCubeCapacity
import Mathlib.Tactic

/-!
# LTR-MAN-54: genuine Connes dual supremum and the eight-dimensional realization

The finite Boolean-cube Dirac spectral construction in MAN-09 uses an
actual Hilbert direct sum of two-dimensional edge blocks. The previous
proof establishes the universal Hamming upper bound and an admissible
observable attaining the Hamming distance for every pair.

Here we package those two inequalities as equality of the literal
extended-real Connes dual supremum, with complex-valued observables and
the genuine bounded Hilbert operator commutator norm.

The two-bit cube has four undirected edges, so this construction has
eight complex scalar Hilbert coordinates. In tandem with the merged
MAN-53 five-dimensional obstruction it bounds the minimal dimension
from above by eight. Excluding dimensions six and seven remains open.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

/-- Complex truth observables in the unit ball of the actual finite
hypercube Dirac commutator operator. -/
def booleanCubeConnesAdmissible (m : ℕ) : Type :=
  { f : BooleanCubeVertex m → ℂ // ‖booleanCubeCommutator f‖ ≤ 1 }

/-- The genuine extended-real dual supremum of observable differences
subject to the complex Hilbert-space commutator norm constraint. -/
noncomputable def booleanCubeConnesDualSupremum
    (m : ℕ) (x y : BooleanCubeVertex m) : ℝ≥0∞ :=
  ⨆ f : booleanCubeConnesAdmissible m,
    (‖f.val x - f.val y‖₊ : ℝ≥0∞)

/-- The actual Connes dual supremum on a finite Boolean hypercube is
exactly its Hamming distance, for all dimensions and vertex pairs. -/
theorem booleanCubeConnesDualSupremum_eq_hamming
    (m : ℕ) (x y : BooleanCubeVertex m) :
    booleanCubeConnesDualSupremum m x y =
      (hammingDist x y : ℝ≥0∞) := by
  obtain ⟨hupper, ⟨w, hw, hweq⟩⟩ :=
    booleanCubeConnesDistance_operator_witness m x y
  apply le_antisymm
  · unfold booleanCubeConnesDualSupremum
    apply iSup_le
    intro f
    have hbound : ‖f.val x - f.val y‖ ≤ (hammingDist x y : ℝ) :=
      hupper f.val f.property
    have hnn : ‖f.val x - f.val y‖₊ ≤ (hammingDist x y : ℝ≥0) := by
      exact_mod_cast hbound
    exact ENNReal.coe_le_coe.mpr hnn
  · have hweqnn :
        (‖w x - w y‖₊ : ℝ≥0∞) =
          (hammingDist x y : ℝ≥0∞) := by
      exact_mod_cast hweq
    rw [← hweqnn]
    unfold booleanCubeConnesDualSupremum
    exact le_iSup
      (fun f : booleanCubeConnesAdmissible m =>
        (‖f.val x - f.val y‖₊ : ℝ≥0∞))
      (⟨w, hw⟩ : booleanCubeConnesAdmissible m)

/-- The two-bit Boolean square has precisely four undirected edges. -/
theorem booleanSquare_edge_count :
    Fintype.card (BooleanCubeEdge 2) = 4 := by
  simpa using booleanCubeEdge_card_succ 1

/-- The unit-edge Hilbert construction for the two-bit Boolean square
contains four two-dimensional blocks, hence eight scalar coordinates. -/
theorem booleanSquare_hilbert_coordinate_count :
    Fintype.card (BooleanCubeEdge 2 × Fin 2) = 8 := by
  simpa using booleanCubeHilbert_coordinate_card_succ 1

/-- In particular, the concrete eight-coordinate Dirac construction
realizes the full exact two-bit Hamming metric as an extended-real
Connes dual supremum of genuine bounded Hilbert commutators. -/
theorem booleanSquare_exactHamming_eightCoordinates
    (x y : BooleanCubeVertex 2) :
    booleanCubeConnesDualSupremum 2 x y =
      (hammingDist x y : ℝ≥0∞) ∧
    Fintype.card (BooleanCubeEdge 2 × Fin 2) = 8 :=
  ⟨booleanCubeConnesDualSupremum_eq_hamming 2 x y,
    booleanSquare_hilbert_coordinate_count⟩

end Neoplatonic.LTR
