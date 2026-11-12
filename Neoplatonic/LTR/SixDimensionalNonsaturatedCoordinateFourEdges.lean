import Neoplatonic.LTR.SixDimensionalSignedCoordinateThreeEdges
import Mathlib.Tactic

/-!
# LTR-MAN-154: the genuine nonsaturated signed coordinates have four edges

MAN-121's three-Hermitian-edge formula for each coordinate requires
the opposite neutral 01-to-10 Dirac coupling to vanish (E12=0).
The nonsaturated six-dimensional existence problem permits that
opposite coupling, so it must appear explicitly.

For the same original Hermitian Dirac matrix, write W=A+B and
J for the undirected 01/10 block of A. The exact identities are:

 A = (00,11)_W/2 + (00,01)_W + (10,11)_W + J
 B = (00,11)_W/2 + (00,10)_W + (01,11)_W - J.

The opposite 01/10 channel enters with opposite signs because the
two Boolean coordinate bits change in opposite directions there.
Both formulas are valid for arbitrary original complex six-coordinate
Dirac matrices, regardless of spectral saturation or fibre pattern.

MAN-153's robust three-channel norm gate must therefore control J
as an additional perturbation when applied to the true nonsaturated
coordinate commutators.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The genuine 01/10 opposite neutral Dirac edge in the first
Boolean coordinate. It need not vanish away from pure saturation. -/
def sixPlusOppositeNeutralEdge
    (label : Fin 6 → Fin 4) (D : SixMat) : SixMat :=
  sixTruthUndirectedBlock label (labelledSquareA label D) 1 2

/-- The full nonsaturated first-coordinate decomposition includes
the otherwise dormant 01/10 opposite neutral exchange channel. -/
noncomputable def sixPlusCoordinateAAllFourEdges
    (label : Fin 6 → Fin 4) (D : SixMat) : SixMat :=
  sixPlusCoordinateAEdges label D +
    sixPlusOppositeNeutralEdge label D

/-- The second coordinate carries that same opposite neutral
channel with reversed sign. -/
noncomputable def sixPlusCoordinateBAllFourEdges
    (label : Fin 6 → Fin 4) (D : SixMat) : SixMat :=
  sixPlusCoordinateBEdges label D -
    sixPlusOppositeNeutralEdge label D

/-- Exact original six-coordinate first Dirac commutator
decomposition, for arbitrary D without a saturation premise. -/
theorem sixLabelled_coordinateA_fourEdges
    (label : Fin 6 → Fin 4) (D : SixMat) :
    labelledSquareA label D =
      sixPlusCoordinateAAllFourEdges label D := by
  ext i j
  generalize hli : label i = u
  generalize hlj : label j = v
  fin_cases u <;> fin_cases v <;>
    simp [hli, hlj, sixPlusCoordinateAAllFourEdges,
      sixPlusCoordinateAEdges, sixPlusActiveHalf,
      sixPlusOppositeNeutralEdge, sixTruthUndirectedBlock,
      sixTruthFibreBlock_entry, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply,
      labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ] <;> ring

/-- Exact original six-coordinate second Dirac commutator
decomposition with the negative 01/10 edge, for arbitrary D. -/
theorem sixLabelled_coordinateB_fourEdges
    (label : Fin 6 → Fin 4) (D : SixMat) :
    labelledSquareB label D =
      sixPlusCoordinateBAllFourEdges label D := by
  ext i j
  generalize hli : label i = u
  generalize hlj : label j = v
  fin_cases u <;> fin_cases v <;>
    simp [hli, hlj, sixPlusCoordinateBAllFourEdges,
      sixPlusCoordinateBEdges, sixPlusActiveHalf,
      sixPlusOppositeNeutralEdge, sixTruthUndirectedBlock,
      sixTruthFibreBlock_entry, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply,
      labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ] <;> ring

end Neoplatonic.LTR
