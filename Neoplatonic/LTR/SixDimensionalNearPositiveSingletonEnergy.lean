import Neoplatonic.LTR.SixDimensionalPauliOppositeEnergyRegions
import Neoplatonic.LTR.SixDimensionalExactHammingPauliSaturation
import Mathlib.Tactic

/-!
# LTR-MAN-158: near-positive Pauli saturation suppresses E12 for singleton opposite fibres

The true six-dimensional Hamming Dirac matrix has oriented opposite
truth-block energies E03,E12. The residual Pauli mixed scalar is
c=2(E03-E12). MAN-81 gives E03 <= min(m00,m11)/4.

In any faithful truth-fibre multiplicity pattern with
min(m00,m11)=1, the positive near-half condition
c >= 1/2-epsilon forces

  0 <= E12 <= epsilon/2,
  1/4-epsilon/2 <= E03 <= 1/4.

Thus the extra 01<->10 fourth edge from MAN-154 has small
Frobenius energy in this region. Converting that energy to its
Hilbert operator norm will complete the fourth-channel input
of MAN-155's robust norm-gap gate.

The exceptional (m00,m11)=(2,2) fibre pattern needs separate
analysis; these inequalities do not assume pure saturation.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- For a singleton opposite 00/11 fibre, near maximum positive
Pauli overlap forces the residual 01/10 opposite energy to be
at most half the overlap slack. -/
theorem sixLabelled_exactHamming_nearPositive_singleton03_energy12_le
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hmin : min (truthMultiplicity label 0)
      (truthMultiplicity label 3) = 1)
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D) :
    (0 : ℝ) ≤ sixTruthFibreBlockEnergy label D 1 2 ∧
    sixTruthFibreBlockEnergy label D 1 2 ≤ epsilon / 2 := by
  obtain ⟨h03, _⟩ :=
    sixLabelled_exactHamming_oppositeBlock_minEnergy label D hD hham
  have h03bound :
      sixTruthFibreBlockEnergy label D 0 3 ≤ (1 / 4 : ℝ) := by
    simpa [hmin] using h03
  have h12nonneg :
      (0 : ℝ) ≤ sixTruthFibreBlockEnergy label D 1 2 :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  have hmixed :
      (1 / 2 : ℝ) - epsilon ≤
        2 * (sixTruthFibreBlockEnergy label D 0 3 -
          sixTruthFibreBlockEnergy label D 1 2) := by
    simpa only [sixOrientedOppositeEnergyImbalance] using hnear
  exact ⟨h12nonneg, by linarith⟩

/-- The same near-positive condition pins the active 00/11
opposite energy within epsilon/2 of one quarter. -/
theorem sixLabelled_exactHamming_nearPositive_singleton03_energy03_band
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hmin : min (truthMultiplicity label 0)
      (truthMultiplicity label 3) = 1)
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D) :
    (1 / 4 : ℝ) - epsilon / 2 ≤
      sixTruthFibreBlockEnergy label D 0 3 ∧
    sixTruthFibreBlockEnergy label D 0 3 ≤ (1 / 4 : ℝ) := by
  obtain ⟨h03, _⟩ :=
    sixLabelled_exactHamming_oppositeBlock_minEnergy label D hD hham
  have h03bound :
      sixTruthFibreBlockEnergy label D 0 3 ≤ (1 / 4 : ℝ) := by
    simpa [hmin] using h03
  have h12nonneg :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  have hmixed :
      (1 / 2 : ℝ) - epsilon ≤
        2 * (sixTruthFibreBlockEnergy label D 0 3 -
          sixTruthFibreBlockEnergy label D 1 2) := by
    simpa only [sixOrientedOppositeEnergyImbalance] using hnear
  exact ⟨by linarith, h03bound⟩

end Neoplatonic.LTR
