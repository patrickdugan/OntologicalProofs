import Neoplatonic.LTR.SixDimensionalNearHalfTraceRigidity
import Neoplatonic.LTR.SixDimensionalSingletonOppositeNeutralEdgeEnergy
import Neoplatonic.LTR.SixDimensionalOppositeEnergyPatterns
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-162: near-half Pauli overlap forces singleton neutral truth fibres

MAN-161 proves the genuine unsaturated positive signed trace bound

  |8 E03 - (6 - 2(m01+m10))| <= 12 epsilon.

For a faithful six-dimensional truth representation, both neutral
truth fibres are nonempty. Positive Pauli overlap c>=1/2-epsilon
forces E03 >= 1/4-epsilon/2, since E12>=0.

If epsilon<1/8, a neutral multiplicity sum of 3 or 4 contradicts
the trace estimate. Thus m01=m10=1, even for the remaining 2+2
opposite-fibre pattern. Substitution back into MAN-161 gives

  E03 <= 1/4 + (3/2)epsilon,
  E12 <= 2 epsilon.

MAN-159 then identifies ||J||^2 = E12 and yields a uniform original
six-dimensional fourth-edge budget ||J||^2 <= 2 epsilon.

All statements concern the original common Hermitian Dirac D;
no pure-saturation or gauge premise is introduced.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Each of the two neutral truth atoms has at least one Hilbert
coordinate in a faithful six-dimensional truth representation. -/
theorem sixTruth_plusNeutral_multiplicity_positive
    (label : Fin 6 → Fin 4) (hsurj : Function.Surjective label) :
    1 ≤ truthMultiplicity label 1 ∧
      1 ≤ truthMultiplicity label 2 := by
  have hp := truthMultiplicity6_complete label hsurj
  simp only [truthMultiplicityPattern6] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨h0, h1, h2, h3⟩
  all_goals simp [h1, h2]

/-- The quantitative trace defect rules out extra neutral-sector
multiplicity under positive near-half Pauli overlap epsilon<1/8. -/
theorem sixLabelled_exactHamming_positiveNearHalf_neutralSingletons
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D)
    (hsmall : epsilon < (1 / 8 : ℝ)) :
    truthMultiplicity label 1 = 1 ∧
      truthMultiplicity label 2 = 1 := by
  let m : ℕ := truthMultiplicity label 1 + truthMultiplicity label 2
  let e03 : ℝ := sixTruthFibreBlockEnergy label D 0 3
  let e12 : ℝ := sixTruthFibreBlockEnergy label D 1 2
  have hpos := sixTruth_plusNeutral_multiplicity_positive label hsurj
  have h12 : 0 ≤ e12 :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  have hnear' : (1 / 2 : ℝ) - epsilon ≤ 2 * (e03 - e12) := hnear
  have h03lower : (1 / 4 : ℝ) - epsilon / 2 ≤ e03 := by
    linarith
  have hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D := by
    linarith
  have htrace := sixLabelled_exactHamming_positiveNearHalf_traceRigidity
    label D hD hham epsilon hc hnear
  change |8 * e03 - (6 - 2 * (m : ℝ))| ≤ 12 * epsilon at htrace
  have hsmallm : m < 3 := by
    by_contra hn
    have hm3 : 3 ≤ m := by omega
    have hm3real : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
    have hUpper : 8 * e03 - (6 - 2 * (m : ℝ)) ≤ 12 * epsilon :=
      (le_abs_self _).trans htrace
    linarith
  have hsum : m = 2 := by
    dsimp [m]
    omega
  dsimp [m] at hsum
  constructor <;> omega

/-- The same trace band places E03 in a narrow interval around
one quarter after the neutral truth fibres have been forced singleton. -/
theorem sixLabelled_exactHamming_positiveNearHalf_E03_upper
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D)
    (hsmall : epsilon < (1 / 8 : ℝ)) :
    sixTruthFibreBlockEnergy label D 0 3 ≤
      (1 / 4 : ℝ) + 3 * epsilon / 2 := by
  obtain ⟨h1, h2⟩ :=
    sixLabelled_exactHamming_positiveNearHalf_neutralSingletons
      label D hsurj hD hham epsilon hnear hsmall
  have hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D := by
    linarith
  have htrace := sixLabelled_exactHamming_positiveNearHalf_traceRigidity
    label D hD hham epsilon hc hnear
  rw [h1, h2] at htrace
  norm_num at htrace
  have hUpper :=
    (le_abs_self (8 * sixTruthFibreBlockEnergy label D 0 3 - 2)).trans htrace
  linarith

/-- Uniform small E12 across all faithful 6D multiplicity patterns,
including (m00,m11)=(2,2), for positive near-half Pauli overlap. -/
theorem sixLabelled_exactHamming_positiveNearHalf_E12_le_twoEpsilon
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D)
    (hsmall : epsilon < (1 / 8 : ℝ)) :
    sixTruthFibreBlockEnergy label D 1 2 ≤ 2 * epsilon := by
  have hup := sixLabelled_exactHamming_positiveNearHalf_E03_upper
    label D hsurj hD hham epsilon hnear hsmall
  have hnear' :
    (1 / 2 : ℝ) - epsilon ≤
      2 * (sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2) := hnear
  linarith

/-- Complete true fourth-channel squared-operator-norm budget
in the positive near-half region for every faithful 6D pattern. -/
theorem sixLabelled_exactHamming_positiveNearHalf_J_normSq_le_twoEpsilon
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D)
    (hsmall : epsilon < (1 / 8 : ℝ)) :
    ‖sixPlusOppositeNeutralEdge label D‖ *
      ‖sixPlusOppositeNeutralEdge label D‖ ≤ 2 * epsilon := by
  obtain ⟨h1, _⟩ :=
    sixLabelled_exactHamming_positiveNearHalf_neutralSingletons
      label D hsurj hD hham epsilon hnear hsmall
  rw [sixLabelled_singletonNeutral1_fourthEdge_normSq_eq_energy12
    label D hD h1]
  exact sixLabelled_exactHamming_positiveNearHalf_E12_le_twoEpsilon
    label D hsurj hD hham epsilon hnear hsmall

end Neoplatonic.LTR
