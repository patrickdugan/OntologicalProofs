import Neoplatonic.LTR.SixDimensionalNeutralEdgeOriginalBridge
import Neoplatonic.LTR.SixDimensionalSignedCoordinateThreeEdges
import Neoplatonic.LTR.SixDimensionalSaturated03TransitionTrace
import Mathlib.Tactic

/-!
# LTR-MAN-129: identify every positive neutral transition with an actual Dirac edge

MAN-127 identifies a generic corner-neutral Hermitian edge with
the corresponding original truth block, once the projector
containment equations P C=P and Q N=N are established.

Here those equations are proved for any original six-dimensional
truth labelling, any corner atom u in {00,11} and neutral atom
v in {01,10}, using the existing exact labelled diagonal
projectors. Thus the MAN-125 orthogonality edges are literally
the MAN-121 signed-coordinate adjacent edge operators.

This is an exact original-coordinate identity, independent of
saturation energy or fibre multiplicity. It uses the Boolean-square
truth-bit convention certified in the merged MAN-126 coordinate split.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Every plus-neutral signed witness transition from an opposite
truth atom u to a neutral truth atom v is the genuine undirected
u-v truth block of the Hermitian Dirac witness. -/
theorem sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (u v : Fin 4)
    (hu : u = 0 ∨ u = 3)
    (hv : v = 1 ∨ v = 2) :
    sixMatrix_neutralUndirectedEdge
      (sixTruthFibreProjection label u)
      (sixTruthFibreProjection label v)
      ((1 - sixTruthSectorProjection label squarePlusNeutral) *
        (labelledSquareA label D + labelledSquareB label D) *
        sixTruthSectorProjection label squarePlusNeutral) =
      sixTruthUndirectedBlock label
        (labelledSquareA label D + labelledSquareB label D) u v := by
  let P : SixMat := sixTruthFibreProjection label u
  let N : SixMat := sixTruthFibreProjection label v
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  change sixMatrix_neutralUndirectedEdge P N (C * W * Q) =
    P * W * N + N * W * P
  have hu1 : u ≠ 1 := by
    rcases hu with hu | hu <;> subst u <;> decide
  have hu2 : u ≠ 2 := by
    rcases hu with hu | hu <;> subst u <;> decide
  have hPN1 : P * sixTruthFibreProjection label 1 = 0 := by
    exact sixTruthFibreProjection_mul_zero_of_distinct label u 1 hu1
  have hPN2 : P * sixTruthFibreProjection label 2 = 0 := by
    exact sixTruthFibreProjection_mul_zero_of_distinct label u 2 hu2
  have hPQ : P * Q = 0 := by
    change P * sixTruthSectorProjection label squarePlusNeutral = 0
    rw [sixPlusNeutral_eq_fibre01_add_fibre10, mul_add, hPN1, hPN2]
    simp
  have hPC : P * C = P := by
    change P * (1 - Q) = P
    rw [mul_sub, mul_one, hPQ, sub_zero]
  have hQN : Q * N = N := by
    rcases hv with hv | hv
    · subst v
      exact (sixPlusNeutral_mul_fibre1_or_fibre2 label).1
    · subst v
      exact (sixPlusNeutral_mul_fibre1_or_fibre2 label).2
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun t : Fin 4 => t = u))
  have hNH : N.IsHermitian := by
    simpa only [N, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun t : Fin 4 => t = v))
  have hWH : W.IsHermitian :=
    sixLabelled_plusWitness_isHermitian label D hD
  exact sixMatrix_neutralUndirectedEdge_eq_originalTruthEdge
    P N C Q W hPH hNH hWH hPC hQN

end Neoplatonic.LTR
