import Neoplatonic.LTR.SixDimensionalSignedOppositeRankOne
import Neoplatonic.LTR.SixDimensionalSignedOppositeRankOneMinus
import Mathlib.Tactic

/-!
# LTR-MAN-121: actual coordinate commutators split into three Hermitian edges

At pure positive Hamming saturation e03=1/4, e12=0,
the original Dirac block joining neutral truth atoms 01 and 10
vanishes identically. Therefore each actual six-dimensional
coordinate commutator is the sum of precisely three undirected
edge operators, indexed by its truth-atom incidence graph.

Write W=A+B for the positive signed witness. The opposite
00/11 block contributes half of W to each coordinate. Each
coordinate also retains two different adjacent edges of W:

 A: (00,11)/2 + (00,10) + (01,11)
 B: (00,11)/2 + (00,01) + (10,11).

This module proves these exact matrix equations directly in
the original Hilbert labelling, without a canonical basis.

The remaining MAN-121+ step is to use MAN-94's XY=0 and
MAN-113's rank-one Gram defects to show the three Hermitian
edge terms multiply pairwise to zero. MAN-120 then turns their
norms into the maximum of the component norms.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The undirected truth-fibre edge of a labelled six-dimensional
matrix, in its original coordinate basis. -/
def sixTruthUndirectedBlock
    (label : Fin 6 → Fin 4) (W : SixMat)
    (u v : Fin 4) : SixMat :=
  sixTruthFibreBlock label W u v +
    sixTruthFibreBlock label W v u

/-- The surviving 00/11 opposite edge, scaled to its contribution
in each individual coordinate commutator. -/
def sixPlusActiveHalf
    (label : Fin 6 → Fin 4) (D : SixMat) : SixMat :=
  (1 / 2 : ℂ) •
    sixTruthUndirectedBlock label
      (labelledSquareA label D + labelledSquareB label D) 0 3

/-- The two adjacent edges of the first coordinate, plus the
shared half opposite corner. -/
def sixPlusCoordinateAEdges
    (label : Fin 6 → Fin 4) (D : SixMat) : SixMat :=
  sixPlusActiveHalf label D +
    sixTruthUndirectedBlock label
      (labelledSquareA label D + labelledSquareB label D) 0 2 +
    sixTruthUndirectedBlock label
      (labelledSquareA label D + labelledSquareB label D) 1 3

/-- The second coordinate retains the complementary two
adjacent edges of the positive signed witness. -/
def sixPlusCoordinateBEdges
    (label : Fin 6 → Fin 4) (D : SixMat) : SixMat :=
  sixPlusActiveHalf label D +
    sixTruthUndirectedBlock label
      (labelledSquareA label D + labelledSquareB label D) 0 1 +
    sixTruthUndirectedBlock label
      (labelledSquareA label D + labelledSquareB label D) 2 3

/-- A zero oriented neutral-opposite block eliminates both
01-to-10 and 10-to-01 original Dirac entries under Hermitianity. -/
theorem sixLabelled_zero12_block_entries
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (i j : Fin 6)
    (hbad : (label i = 1 ∧ label j = 2) ∨
      (label i = 2 ∧ label j = 1)) :
    D i j = 0 := by
  have hBlock12 : sixTruthFibreBlock label D 1 2 = 0 :=
    (sixTruthFibreBlockEnergy_zero_iff_block_zero label D 1 2).mp h12
  have hBlock21 : sixTruthFibreBlock label D 2 1 = 0 :=
    sixTruthFibreBlock_zero_reverse label D hD 1 2 hBlock12
  rcases hbad with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · have he := congrArg (fun M : SixMat => M i j) hBlock12
    simpa [sixTruthFibreBlock_entry, hi, hj] using he
  · have he := congrArg (fun M : SixMat => M i j) hBlock21
    simpa [sixTruthFibreBlock_entry, hi, hj] using he

/-- Under pure positive saturation, the actual first coordinate
commutator is precisely the sum of its three Hermitian edges. -/
theorem sixLabelled_exactHamming_zero12_coordinateA_threeEdges
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    labelledSquareA label D = sixPlusCoordinateAEdges label D := by
  ext i j
  by_cases hbad : (label i = 1 ∧ label j = 2) ∨
      (label i = 2 ∧ label j = 1)
  · have hz := sixLabelled_zero12_block_entries
      label D hD h12 i j hbad
    simp [sixPlusCoordinateAEdges, sixPlusActiveHalf,
      sixTruthUndirectedBlock, sixTruthFibreBlock_entry,
      Matrix.add_apply, Matrix.smul_apply, labelledSquareA,
      labelledSquareB, hz]
  · generalize hli : label i = u
    generalize hlj : label j = v
    fin_cases u <;> fin_cases v <;>
      simp_all [sixPlusCoordinateAEdges, sixPlusActiveHalf,
        sixTruthUndirectedBlock, sixTruthFibreBlock_entry,
        Matrix.add_apply, Matrix.smul_apply, labelledSquareA,
        labelledSquareB, squareTruthBitP, squareTruthBitQ] <;> ring

/-- The actual second coordinate decomposes into its own
two adjacent edges plus the common opposite half-edge. -/
theorem sixLabelled_exactHamming_zero12_coordinateB_threeEdges
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    labelledSquareB label D = sixPlusCoordinateBEdges label D := by
  ext i j
  by_cases hbad : (label i = 1 ∧ label j = 2) ∨
      (label i = 2 ∧ label j = 1)
  · have hz := sixLabelled_zero12_block_entries
      label D hD h12 i j hbad
    simp [sixPlusCoordinateBEdges, sixPlusActiveHalf,
      sixTruthUndirectedBlock, sixTruthFibreBlock_entry,
      Matrix.add_apply, Matrix.smul_apply, labelledSquareA,
      labelledSquareB, hz]
  · generalize hli : label i = u
    generalize hlj : label j = v
    fin_cases u <;> fin_cases v <;>
      simp_all [sixPlusCoordinateBEdges, sixPlusActiveHalf,
        sixTruthUndirectedBlock, sixTruthFibreBlock_entry,
        Matrix.add_apply, Matrix.smul_apply, labelledSquareA,
        labelledSquareB, squareTruthBitP, squareTruthBitQ] <;> ring

/-- Each undirected truth edge of a Hermitian matrix is
itself Hermitian. -/
theorem sixTruthUndirectedBlock_hermitian
    (label : Fin 6 → Fin 4) (W : SixMat)
    (hW : W.IsHermitian) (u v : Fin 4) :
    (sixTruthUndirectedBlock label W u v).IsHermitian := by
  have hEntries : ∀ i j, W i j = star (W j i) := by
    intro i j
    have h := congrArg (fun M : SixMat => M i j) hW.eq
    simpa only [Matrix.conjTranspose_apply] using h.symm
  have hblock :
      (sixTruthFibreBlock label W u v).conjTranspose =
        sixTruthFibreBlock label W v u :=
    sixTruthFibreBlock_conjTranspose label W hEntries u v
  change (sixTruthUndirectedBlock label W u v).conjTranspose =
    sixTruthUndirectedBlock label W u v
  dsimp [sixTruthUndirectedBlock]
  rw [Matrix.conjTranspose_add, hblock]
  have hreverse :
      (sixTruthFibreBlock label W v u).conjTranspose =
        sixTruthFibreBlock label W u v := by
    rw [← hblock, Matrix.conjTranspose_conjTranspose]
  rw [hreverse]
  abel

end Neoplatonic.LTR
