import Neoplatonic.LTR.SixDimensionalSignedWitnessTraceEnergy
import Mathlib.Tactic

/-!
# LTR-MAN-92: six faithful truth-fibre patterns at saturated Pauli overlap

MAN-85 gives the sharp |e03-e12| ≤ 1/4 bound for the actual
six-dimensional exact-Hamming Hermitian Dirac representation.

For the eight multiplicity patterns with both opposite-pair minima
one, saturation forces one opposite Dirac energy equal to 1/4 and
the other zero (MAN-85/86). MAN-91 promotes the surviving signed
witness to a true ambient 6×6 involution.

The new MAN-92 trace identity then forces the two truth atoms on
the neutral opposite diagonal to be singletons. Because all four
truth fibres are nonempty and the Hilbert dimension is six, the
surviving opposite diagonal has total multiplicity four, split as
1+3, 2+2, or 3+1.

This leaves six possible labelled fibre assignments at saturation:
three for 00--11 survival and their three 01--10 counterparts.
The four adjacent-double assignments are thereby excluded under
the explicit maximum-overlap and min-one premises.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Exact-Hamming 00--11 saturation forces both 01 and 10
truth fibres to be one-dimensional in every faithful chart. -/
theorem sixLabelled_saturated03_neutralFibres_singleton
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    truthMultiplicity label 1 = 1 ∧
      truthMultiplicity label 2 = 1 := by
  have hW := sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution
    label D hD hham h03 h12
  have hs := sixLabelled_plusWitness_saturated_neutral_fibreSum_two
    label D hD hW h03
  have h1 := truthMultiplicity_pos label hsurj 1
  have h2 := truthMultiplicity_pos label hsurj 2
  omega

/-- Exact-Hamming 01--10 saturation makes the 00 and 11
neutral truth fibres singletons. -/
theorem sixLabelled_saturated12_neutralFibres_singleton
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    truthMultiplicity label 0 = 1 ∧
      truthMultiplicity label 3 = 1 := by
  have hW := sixLabelled_exactHamming_saturated12_trueMatrixMinus_involution
    label D hD hham h03 h12
  have hs := sixLabelled_minusWitness_saturated_neutral_fibreSum_two
    label D hD hW h12
  have h0 := truthMultiplicity_pos label hsurj 0
  have h3 := truthMultiplicity_pos label hsurj 3
  omega

/-- The surviving opposite diagonal has multiplicities (1,3),
(2,2), or (3,1), and the neutral diagonal has multiplicities (1,1).
The six disjuncts are the labelled saturated-trace fibre patterns. -/
def sixDimSaturatedTraceFibrePattern
    (m0 m1 m2 m3 : ℕ) : Prop :=
  (m1 = 1 ∧ m2 = 1 ∧
    ((m0 = 1 ∧ m3 = 3) ∨
     (m0 = 2 ∧ m3 = 2) ∨
     (m0 = 3 ∧ m3 = 1))) ∨
  (m0 = 1 ∧ m3 = 1 ∧
    ((m1 = 1 ∧ m2 = 3) ∨
     (m1 = 2 ∧ m2 = 2) ∨
     (m1 = 3 ∧ m2 = 1)))

/-- In a faithful six-dimensional exact-Hamming chart, if both
opposite-pair minimum multiplicities are one and the real Pauli
mixed coefficient saturates its sharp bound, then only the six
precise truth-fibre multiplicity patterns above remain possible. -/
theorem sixLabelled_exactHamming_minOne_saturation_sixFibreCases
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hmin03 : min (truthMultiplicity label 0)
      (truthMultiplicity label 3) = 1)
    (hmin12 : min (truthMultiplicity label 1)
      (truthMultiplicity label 2) = 1)
    (hsat : |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ)) :
    sixDimSaturatedTraceFibrePattern
      (truthMultiplicity label 0)
      (truthMultiplicity label 1)
      (truthMultiplicity label 2)
      (truthMultiplicity label 3) := by
  have hs : truthMultiplicity label 0 +
      truthMultiplicity label 1 +
      truthMultiplicity label 2 +
      truthMultiplicity label 3 = 6 := by
    simpa only [Fin.sum_univ_four] using truthMultiplicity_sum label
  have hpos0 := truthMultiplicity_pos label hsurj 0
  have hpos1 := truthMultiplicity_pos label hsurj 1
  have hpos2 := truthMultiplicity_pos label hsurj 2
  have hpos3 := truthMultiplicity_pos label hsurj 3
  rcases sixLabelled_exactHamming_minOne_saturation_energyExclusive
      label D hD hham hmin03 hmin12 hsat with
    ⟨h03, h12⟩ | ⟨h03, h12⟩
  · obtain ⟨h1, h2⟩ :=
      sixLabelled_saturated03_neutralFibres_singleton
        label D hsurj hD hham h03 h12
    change (truthMultiplicity label 1 = 1 ∧
      truthMultiplicity label 2 = 1 ∧
      ((truthMultiplicity label 0 = 1 ∧ truthMultiplicity label 3 = 3) ∨
       (truthMultiplicity label 0 = 2 ∧ truthMultiplicity label 3 = 2) ∨
       (truthMultiplicity label 0 = 3 ∧ truthMultiplicity label 3 = 1))) ∨ _
    omega
  · obtain ⟨h0, h3⟩ :=
      sixLabelled_saturated12_neutralFibres_singleton
        label D hsurj hD hham h03 h12
    change _ ∨ (truthMultiplicity label 0 = 1 ∧
      truthMultiplicity label 3 = 1 ∧
      ((truthMultiplicity label 1 = 1 ∧ truthMultiplicity label 2 = 3) ∨
       (truthMultiplicity label 1 = 2 ∧ truthMultiplicity label 2 = 2) ∨
       (truthMultiplicity label 1 = 3 ∧ truthMultiplicity label 2 = 1)))
    omega

/-- The four adjacent-double six-dimensional fibre multiplicity
patterns from MAN-73 cannot occur at maximum real Pauli overlap
under the exact-Hamming and min-one hypotheses. -/
theorem sixLabelled_exactHamming_minOne_saturation_noAdjacentDoubles
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hmin03 : min (truthMultiplicity label 0)
      (truthMultiplicity label 3) = 1)
    (hmin12 : min (truthMultiplicity label 1)
      (truthMultiplicity label 2) = 1)
    (hsat : |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ)) :
    ¬ sixDimAdjacentDoubles
      (truthMultiplicity label 0)
      (truthMultiplicity label 1)
      (truthMultiplicity label 2)
      (truthMultiplicity label 3) := by
  have hs := sixLabelled_exactHamming_minOne_saturation_sixFibreCases
    label D hsurj hD hham hmin03 hmin12 hsat
  dsimp [sixDimSaturatedTraceFibrePattern] at hs
  intro hadj
  dsimp [sixDimAdjacentDoubles] at hadj
  omega

end Neoplatonic.LTR
