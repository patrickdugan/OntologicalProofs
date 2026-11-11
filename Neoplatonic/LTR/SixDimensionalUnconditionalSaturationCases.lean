import Neoplatonic.LTR.SixDimensionalSaturatedFibreClassification
import Mathlib.Tactic

/-!
# LTR-MAN-92: six-case theorem without a separate minimum-fibre premise

The MAN-92 six-pattern theorem was first established under the
additional premises that the smaller endpoint dimension on each
opposite truth diagonal is one.

These premises are AUTOMATIC for every adjacent-double fibre
assignment, because a pair of adjacent doubled truth vertices
leaves one singleton on each opposite pair. Thus the trace
exclusion theorem rules out adjacent-double patterns under
faithfulness, Hermitianity, exact Hamming distances, and maximal
Pauli energy imbalance alone.

MAN-55's exhaustive faithful six-dimensional multiplicity
classification then leaves exactly six *candidate* patterns:
four triples and two opposite-double assignments. This remains
a necessary condition and makes no assertion of realizability.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Every adjacent-double labelled six-dimensional pattern has
a singleton endpoint on each of the two opposite diagonals. -/
theorem sixDimAdjacentDoubles_oppositeMinima_one
    (m0 m1 m2 m3 : ℕ)
    (h : sixDimAdjacentDoubles m0 m1 m2 m3) :
    min m0 m3 = 1 ∧ min m1 m2 = 1 := by
  rcases h with h | h | h | h
  all_goals rcases h with ⟨h0, h1, h2, h3⟩
  all_goals simp [h0, h1, h2, h3]

/-- Maximal oriented opposite-corner energy imbalance under
exact six-dimensional Hamming distances rules out every
adjacent-double fibre assignment, without extra multiplicity
assumptions. -/
theorem sixLabelled_exactHamming_saturation_noAdjacentDoubles
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hsat : |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ)) :
    ¬ sixDimAdjacentDoubles
      (truthMultiplicity label 0)
      (truthMultiplicity label 1)
      (truthMultiplicity label 2)
      (truthMultiplicity label 3) := by
  intro hadj
  obtain ⟨hm03, hm12⟩ :=
    sixDimAdjacentDoubles_oppositeMinima_one
      _ _ _ _ hadj
  exact (sixLabelled_exactHamming_minOne_saturation_noAdjacentDoubles
    label D hsurj hD hham hm03 hm12 hsat) hadj

/-- Faithful multiplicities summing to six, with adjacent-double
patterns removed, belong to exactly the six remaining labelled
triple-fibre and opposite-double patterns. -/
theorem sixTruthFibre_noAdjacent_sixCases
    (label : Fin 6 → Fin 4)
    (hsurj : Function.Surjective label)
    (hno : ¬ sixDimAdjacentDoubles
      (truthMultiplicity label 0)
      (truthMultiplicity label 1)
      (truthMultiplicity label 2)
      (truthMultiplicity label 3)) :
    sixDimSaturatedTraceFibrePattern
      (truthMultiplicity label 0)
      (truthMultiplicity label 1)
      (truthMultiplicity label 2)
      (truthMultiplicity label 3) := by
  have hp := truthMultiplicity6_complete label hsurj
  simp only [truthMultiplicityPattern6] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨h0, h1, h2, h3⟩
  all_goals simp_all [sixDimSaturatedTraceFibrePattern, sixDimAdjacentDoubles]

/-- The definitive MAN-92 combinatorial consequence:
Every faithful complex six-dimensional exact-Hamming spectral
representation saturating the residual Pauli overlap must
have one of the six permitted fibre multiplicity patterns.
The sharp overlap assumption is explicit; no min-one premise
is needed and no existence claim is made. -/
theorem sixLabelled_exactHamming_saturation_sixFibreCases
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hsat : |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ)) :
    sixDimSaturatedTraceFibrePattern
      (truthMultiplicity label 0)
      (truthMultiplicity label 1)
      (truthMultiplicity label 2)
      (truthMultiplicity label 3) := by
  exact sixTruthFibre_noAdjacent_sixCases label hsurj
    (sixLabelled_exactHamming_saturation_noAdjacentDoubles
      label D hsurj hD hham hsat)

end Neoplatonic.LTR
