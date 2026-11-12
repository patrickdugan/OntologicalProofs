import Neoplatonic.LTR.SixDimensionalSingletonOppositeNeutralEdgeEnergy
import Neoplatonic.LTR.SixDimensionalNearPositiveSingletonEnergy
import Mathlib.Tactic

/-!
# LTR-MAN-160: the true fourth Dirac channel satisfies the near-half error budget

MAN-158 proves E12 <= epsilon/2 when the positive signed residual
Pauli overlap is within epsilon of one half and one of the 00/11
truth fibres is a singleton.

MAN-159 proves the exact operator-norm identity ||J||^2 = E12
when at least one of the 01/10 truth fibres is a singleton.

Combining those original-coordinate Lean certificates supplies
the fourth-channel hypothesis of MAN-155 for the corresponding
faithful six-dimensional multiplicity patterns.

The scalar delta budget is stated without sqrt, so it can be
inserted directly into the four-channel norm gate.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Positive near-half Pauli overlap bounds the squared Euclidean
operator norm of the actual fourth 01/10 edge by epsilon/2, whenever
the opposite 00/11 pair and the neutral 01/10 pair each contain
a singleton truth fibre. -/
theorem sixLabelled_exactHamming_positiveNearHalf_singletonFourthEdge_normSq_le
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hmin03 : min (truthMultiplicity label 0)
      (truthMultiplicity label 3) = 1)
    (hmin12 : truthMultiplicity label 1 = 1 ∨
      truthMultiplicity label 2 = 1)
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D) :
    ‖sixPlusOppositeNeutralEdge label D‖ *
      ‖sixPlusOppositeNeutralEdge label D‖ ≤ epsilon / 2 := by
  rw [sixLabelled_singletonNeutralEither_fourthEdge_normSq_eq_energy12
    label D hD hmin12]
  exact (sixLabelled_exactHamming_nearPositive_singleton03_energy12_le
    label D hD hham hmin03 epsilon hnear).2

/-- For any nonnegative delta with delta^2 >= epsilon/2, the
actual fourth Dirac channel satisfies the norm input required
by MAN-155's robust four-edge obstruction. -/
theorem sixLabelled_exactHamming_positiveNearHalf_singletonFourthEdge_norm_le
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hmin03 : min (truthMultiplicity label 0)
      (truthMultiplicity label 3) = 1)
    (hmin12 : truthMultiplicity label 1 = 1 ∨
      truthMultiplicity label 2 = 1)
    (epsilon delta : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D)
    (hdeltaNonneg : 0 ≤ delta)
    (hdeltaSq : epsilon / 2 ≤ delta * delta) :
    ‖sixPlusOppositeNeutralEdge label D‖ ≤ delta := by
  let J : SixMat := sixPlusOppositeNeutralEdge label D
  have hJ := sixLabelled_exactHamming_positiveNearHalf_singletonFourthEdge_normSq_le
    label D hD hham hmin03 hmin12 epsilon hnear
  change ‖J‖ * ‖J‖ ≤ epsilon / 2 at hJ
  have hJdelta : ‖J‖ * ‖J‖ ≤ delta * delta :=
    hJ.trans hdeltaSq
  by_contra hn
  have hgt : delta < ‖J‖ := lt_of_not_ge hn
  have hsum : 0 < ‖J‖ + delta := by
    linarith [norm_nonneg J]
  have hprod : 0 < (‖J‖ - delta) * (‖J‖ + delta) :=
    mul_pos (by linarith) hsum
  nlinarith

end Neoplatonic.LTR
