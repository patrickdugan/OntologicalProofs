import Neoplatonic.LTR.SixDimensionalNonsaturatedCoordinateFourEdges
import Neoplatonic.LTR.SixDimensionalSignedWitnessPartialIsometry
import Mathlib.Tactic

/-!
# LTR-MAN-156: the fourth nonsaturated Dirac coordinate edge is Hermitian

MAN-154 decomposes the genuine nonsaturated signed coordinates into
four original truth edges. Its extra opposite-neutral channel
J is the undirected 01/10 block of the first imaginary coordinate
commutator A.

For Hermitian D, the two original signed witnesses W₊=A+B and
W₋=A-B are Hermitian. Their half-sum is the true A, so A is
Hermitian as well. The original undirected truth-edge operation
preserves Hermitianity, hence J itself is Hermitian.

This completes the structural hypotheses for applying MAN-155's
four-channel C*-norm theorem to the actual labelled 6D Dirac chart.
The quantitative J norm bound remains a separate obligation.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The first imaginary coordinate Dirac commutator is Hermitian
whenever the original six-dimensional Dirac matrix is Hermitian. -/
theorem sixLabelled_firstCoordinate_isHermitian
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    (labelledSquareA label D).IsHermitian := by
  let A : SixMat := labelledSquareA label D
  let B : SixMat := labelledSquareB label D
  have hplus : (A + B).IsHermitian :=
    sixLabelled_plusWitness_isHermitian label D hD
  have hminus : (A - B).IsHermitian :=
    sixLabelled_minusWitness_isHermitian label D hD
  have hpair : ((A + B) + (A - B)).IsHermitian :=
    hplus.add hminus
  have hA : A = (1 / 2 : ℂ) • ((A + B) + (A - B)) := by
    ext i j
    simp [Matrix.smul_apply, Matrix.add_apply,
      Matrix.sub_apply, smul_eq_mul]
    ring
  have hScaled :
      ((1 / 2 : ℂ) • ((A + B) + (A - B))).IsHermitian := by
    change ((1 / 2 : ℂ) • ((A + B) + (A - B))).conjTranspose =
      (1 / 2 : ℂ) • ((A + B) + (A - B))
    rw [Matrix.conjTranspose_smul, hpair.eq]
    norm_num
  change A.IsHermitian
  rw [hA]
  exact hScaled

/-- The additional 01/10 original Dirac edge is Hermitian.
It is the fourth channel of each nonsaturated coordinate. -/
theorem sixPlusOppositeNeutralEdge_isHermitian
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    (sixPlusOppositeNeutralEdge label D).IsHermitian := by
  exact sixTruthUndirectedBlock_hermitian label
    (labelledSquareA label D)
    (sixLabelled_firstCoordinate_isHermitian label D hD) 1 2

end Neoplatonic.LTR
