import Neoplatonic.LTR.SixSevenFibrePatterns
import Neoplatonic.LTR.TwoBitSquareSupport
import Mathlib.Tactic

/-!
# LTR-MAN-73: truth-fibre branching budgets in dimensions 6 and 7

MAN-55 classifies the multiplicities of all faithful Fin 6 → Fin 4
and Fin 7 → Fin 4 truth-atom labelings.

At a Boolean square vertex, two incident nonzero edge couplings
represent two different coordinate directions. Under an ordered
zero-product hypothesis, the two incident maps cannot both be
nonzero through a one-dimensional complex fibre (MAN-16).
We encode that fibre-dimension consequence as a separate premise.

Each vertex with two incident edges then costs at least one extra
Hilbert coordinate beyond the four required by faithfulness:

  4 + (# branch vertices) ≤ (Hilbert dimension).

For six Hilbert coordinates, any three-edge support satisfying
this necessary branch condition has exactly two adjacent doubled
truth fibres. A full four-edge square needs at least eight coordinates.

This module supplies the precise finite combinatorial obstruction.
The bridge from actual six-dimensional commutator block products to
the branch premise remains a separate analytic obligation. MAN-57
shows that abstract six-dimensional contraction hypotheses by
themselves can allow nonzero residual ordered products.
-/

namespace Neoplatonic.LTR

/-- A necessary support/fibre condition for two commuting
ordered coordinate products: a truth vertex incident to both
independent square edges must have fibre multiplicity at least 2.
The condition is kept explicit pending the six-dimensional
Dirac-block integration. -/
def squareBranchSupported {n : ℕ}
    (label : Fin n → Fin 4) (a b c d : Bool) : Prop :=
  ((a && b) = true → 2 ≤ truthMultiplicity label 0) ∧
  ((a && c) = true → 2 ≤ truthMultiplicity label 1) ∧
  ((b && d) = true → 2 ≤ truthMultiplicity label 2) ∧
  ((c && d) = true → 2 ≤ truthMultiplicity label 3)

/-- One unit of mandatory fibre dimension, and another for
every supported branching event. -/
private theorem bool_branch_dimension
    (e : Bool) (m : ℕ)
    (hpos : 1 ≤ m) (hbranch : e = true → 2 ≤ m) :
    1 + twoBitEdgeWeight e ≤ m := by
  cases e <;> simp_all [twoBitEdgeWeight] <;> omega

/-- In any faithful representation, the number of truth-fibre
branch vertices cannot exceed the excess Hilbert dimension above 4.
This is independent of how the six or seven Hilbert coordinates are
permuted or which truth atoms carry duplicate coordinates. -/
theorem squareBranchSupported_dimension_budget {n : ℕ}
    (label : Fin n → Fin 4)
    (hsurj : Function.Surjective label)
    (a b c d : Bool)
    (hbranch : squareBranchSupported label a b c d) :
    4 + twoBitSquareBranchCount a b c d ≤ n := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hbranch
  have h0 := bool_branch_dimension (a && b)
    (truthMultiplicity label 0)
    (truthMultiplicity_pos label hsurj 0) hb0
  have h1 := bool_branch_dimension (a && c)
    (truthMultiplicity label 1)
    (truthMultiplicity_pos label hsurj 1) hb1
  have h2 := bool_branch_dimension (b && d)
    (truthMultiplicity label 2)
    (truthMultiplicity_pos label hsurj 2) hb2
  have h3 := bool_branch_dimension (c && d)
    (truthMultiplicity label 3)
    (truthMultiplicity_pos label hsurj 3) hb3
  have hs : truthMultiplicity label 0 +
      truthMultiplicity label 1 + truthMultiplicity label 2 +
      truthMultiplicity label 3 = n := by
    simpa only [Fin.sum_univ_four] using truthMultiplicity_sum label
  dsimp [twoBitSquareBranchCount]
  omega

/-- All four Boolean-square edges can be supported through
zero-product-compatible branch fibres only in dimension at least 8. -/
theorem squareBranchSupported_fourEdges_dimension_eight {n : ℕ}
    (label : Fin n → Fin 4)
    (hsurj : Function.Surjective label)
    (hbranch : squareBranchSupported label true true true true) :
    8 ≤ n := by
  have h := squareBranchSupported_dimension_budget
    label hsurj true true true true hbranch
  norm_num [twoBitSquareBranchCount, twoBitEdgeWeight] at h
  omega

/-- In six Hilbert dimensions the branch count is at most two. -/
theorem squareBranchSupported_sixDim_branchCount
    (label : Fin 6 → Fin 4) (hsurj : Function.Surjective label)
    (a b c d : Bool)
    (hbranch : squareBranchSupported label a b c d) :
    twoBitSquareBranchCount a b c d ≤ 2 := by
  have h := squareBranchSupported_dimension_budget
    label hsurj a b c d hbranch
  omega

/-- Precisely the four patterns with two *adjacent* doubled truth
fibres. Their locations are 00/01, 00/10, 01/11, or 10/11,
using the canonical 00,01,10,11 vertex order. -/
def sixDimAdjacentDoubles (m0 m1 m2 m3 : ℕ) : Prop :=
  (m0 = 2 ∧ m1 = 2 ∧ m2 = 1 ∧ m3 = 1) ∨
  (m0 = 2 ∧ m1 = 1 ∧ m2 = 2 ∧ m3 = 1) ∨
  (m0 = 1 ∧ m1 = 2 ∧ m2 = 1 ∧ m3 = 2) ∨
  (m0 = 1 ∧ m1 = 1 ∧ m2 = 2 ∧ m3 = 2)

/-- A three-edge square support requires two branches. In six
dimensions, the excess-two budget forces exactly three edges, and
the two branch vertices are exactly the doubled *adjacent* truth
fibres. This excludes the triple-fibre (3,1,1,1) case and the
opposite-double (2,2,1,1) placements under the branch premise. -/
theorem squareBranchSupported_sixDim_threeEdges_adjacentDoubles
    (label : Fin 6 → Fin 4) (hsurj : Function.Surjective label)
    (a b c d : Bool)
    (hbranch : squareBranchSupported label a b c d)
    (hthree : 3 ≤ twoBitSquareEdgeCount a b c d) :
    twoBitSquareEdgeCount a b c d = 3 ∧
    sixDimAdjacentDoubles
      (truthMultiplicity label 0) (truthMultiplicity label 1)
      (truthMultiplicity label 2) (truthMultiplicity label 3) := by
  have hbudget :=
    squareBranchSupported_dimension_budget label hsurj a b c d hbranch
  have hs : truthMultiplicity label 0 +
      truthMultiplicity label 1 + truthMultiplicity label 2 +
      truthMultiplicity label 3 = 6 := by
    simpa only [Fin.sum_univ_four] using truthMultiplicity_sum label
  have h0 := truthMultiplicity_pos label hsurj 0
  have h1 := truthMultiplicity_pos label hsurj 1
  have h2 := truthMultiplicity_pos label hsurj 2
  have h3 := truthMultiplicity_pos label hsurj 3
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hbranch
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [twoBitSquareEdgeCount, twoBitSquareBranchCount,
      twoBitEdgeWeight, sixDimAdjacentDoubles] <;> omega

/-- A faithful seven-dimensional representation also lacks the
branch capacity for a complete four-edge support. -/
theorem squareBranchSupported_sevenDim_noFullSquare
    (label : Fin 7 → Fin 4) (hsurj : Function.Surjective label)
    (hbranch : squareBranchSupported label true true true true) :
    False := by
  have h := squareBranchSupported_fourEdges_dimension_eight
    label hsurj hbranch
  omega

end Neoplatonic.LTR
