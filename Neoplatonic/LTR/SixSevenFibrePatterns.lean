import Neoplatonic.LTR.FiveFibreFaithfulLabels
import Mathlib.Tactic

/-!
# LTR-MAN-55: exhaustive faithful six/seven-dimensional truth-fibre patterns

A faithful diagonal representation of the four-atom algebra ℂ⁴ on a
Hilbert space of dimension n corresponds to a surjective label
Fin n → Fin 4. Its four nonempty fibres have positive cardinalities
whose sum equals n.

For dimension six, the only partitions are (3,1,1,1) and
(2,2,1,1). For dimension seven, the only partitions are (4,1,1,1),
(3,2,1,1) and (2,2,2,1), up to permutation of the truth atoms.

The formal predicates enumerate each assignment of multiplicities
to the four named truth values. The proofs use the genuine fibre
cardinalities and arithmetic completeness, without metric assumptions.
-/

namespace Neoplatonic.LTR

/-- Multiplicity of a truth atom among n Hilbert basis coordinates. -/
def truthMultiplicity {n : ℕ}
    (label : Fin n → Fin 4) (v : Fin 4) : ℕ :=
  (Finset.univ.filter fun i : Fin n => label i = v).card

/-- Four truth-fibre dimensions add up to the Hilbert dimension. -/
theorem truthMultiplicity_sum {n : ℕ} (label : Fin n → Fin 4) :
    (∑ v : Fin 4, truthMultiplicity label v) = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := label) (s := Finset.univ) (t := Finset.univ)
    (by intro i hi; exact Finset.mem_univ _)
  simpa [truthMultiplicity] using h.symm

/-- Every truth atom has a nonzero fibre in a faithful labeling. -/
theorem truthMultiplicity_pos {n : ℕ}
    (label : Fin n → Fin 4)
    (hsurj : Function.Surjective label)
    (v : Fin 4) : 1 ≤ truthMultiplicity label v := by
  obtain ⟨i, hi⟩ := hsurj v
  have hmem : i ∈ Finset.univ.filter (fun j : Fin n => label j = v) := by
    simp [hi]
  have hpos : 0 < (Finset.univ.filter
      (fun j : Fin n => label j = v)).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  dsimp [truthMultiplicity]
  omega

/-- Exhaustive fibre multiplicity patterns for 6 Hilbert coordinates,
    before considering symmetries of the Boolean square. -/
def truthMultiplicityPattern6 (a b c d : ℕ) : Prop :=
  (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 3) ∨
  (a = 1 ∧ b = 1 ∧ c = 3 ∧ d = 1) ∨
  (a = 1 ∧ b = 3 ∧ c = 1 ∧ d = 1) ∨
  (a = 3 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
  (a = 1 ∧ b = 1 ∧ c = 2 ∧ d = 2) ∨
  (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 2) ∨
  (a = 1 ∧ b = 2 ∧ c = 2 ∧ d = 1) ∨
  (a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 2) ∨
  (a = 2 ∧ b = 1 ∧ c = 2 ∧ d = 1) ∨
  (a = 2 ∧ b = 2 ∧ c = 1 ∧ d = 1)

/-- Exhaustive fibre multiplicity patterns for 7 Hilbert coordinates,
    before considering symmetries of the Boolean square. -/
def truthMultiplicityPattern7 (a b c d : ℕ) : Prop :=
  (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 4) ∨
  (a = 1 ∧ b = 1 ∧ c = 4 ∧ d = 1) ∨
  (a = 1 ∧ b = 4 ∧ c = 1 ∧ d = 1) ∨
  (a = 4 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
  (a = 1 ∧ b = 1 ∧ c = 2 ∧ d = 3) ∨
  (a = 1 ∧ b = 1 ∧ c = 3 ∧ d = 2) ∨
  (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 3) ∨
  (a = 1 ∧ b = 2 ∧ c = 3 ∧ d = 1) ∨
  (a = 1 ∧ b = 3 ∧ c = 1 ∧ d = 2) ∨
  (a = 1 ∧ b = 3 ∧ c = 2 ∧ d = 1) ∨
  (a = 2 ∧ b = 1 ∧ c = 1 ∧ d = 3) ∨
  (a = 2 ∧ b = 1 ∧ c = 3 ∧ d = 1) ∨
  (a = 2 ∧ b = 3 ∧ c = 1 ∧ d = 1) ∨
  (a = 3 ∧ b = 1 ∧ c = 1 ∧ d = 2) ∨
  (a = 3 ∧ b = 1 ∧ c = 2 ∧ d = 1) ∨
  (a = 3 ∧ b = 2 ∧ c = 1 ∧ d = 1) ∨
  (a = 1 ∧ b = 2 ∧ c = 2 ∧ d = 2) ∨
  (a = 2 ∧ b = 1 ∧ c = 2 ∧ d = 2) ∨
  (a = 2 ∧ b = 2 ∧ c = 1 ∧ d = 2) ∨
  (a = 2 ∧ b = 2 ∧ c = 2 ∧ d = 1)

-- Isolating four numerical variables keeps the exhaustive omega proofs small.
private theorem truthMultiplicityPattern6_of_sum
    (a b c d : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hsum : a + b + c + d = 6) :
    truthMultiplicityPattern6 a b c d := by
  have ha' : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  have hb' : b = 1 ∨ b = 2 ∨ b = 3 := by omega
  rcases ha' with ha' | ha' | ha' <;>
    rcases hb' with hb' | hb' | hb' <;>
    simp [truthMultiplicityPattern6, ha', hb'] <;> omega

-- All 20 positive partitions of seven are checked on four natural variables.
set_option maxHeartbeats 1200000 in
private theorem truthMultiplicityPattern7_of_sum
    (a b c d : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hsum : a + b + c + d = 7) :
    truthMultiplicityPattern7 a b c d := by
  have ha' : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
  have hb' : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
  rcases ha' with ha' | ha' | ha' | ha' <;>
    rcases hb' with hb' | hb' | hb' | hb' <;>
    simp [truthMultiplicityPattern7, ha', hb'] <;> omega

/-- Every faithful diagonal representation of ℂ⁴ on ℂ^6 has
    exactly one of the listed atomic dimension partitions. -/
theorem truthMultiplicity6_complete
    (label : Fin 6 → Fin 4)
    (hsurj : Function.Surjective label) :
    truthMultiplicityPattern6
      (truthMultiplicity label 0) (truthMultiplicity label 1)
      (truthMultiplicity label 2) (truthMultiplicity label 3) := by
  apply truthMultiplicityPattern6_of_sum
  · exact truthMultiplicity_pos label hsurj 0
  · exact truthMultiplicity_pos label hsurj 1
  · exact truthMultiplicity_pos label hsurj 2
  · exact truthMultiplicity_pos label hsurj 3
  · simpa only [Fin.sum_univ_four] using truthMultiplicity_sum label

/-- Every faithful diagonal representation of ℂ⁴ on ℂ^7 has
    exactly one of the listed atomic dimension partitions. -/
theorem truthMultiplicity7_complete
    (label : Fin 7 → Fin 4)
    (hsurj : Function.Surjective label) :
    truthMultiplicityPattern7
      (truthMultiplicity label 0) (truthMultiplicity label 1)
      (truthMultiplicity label 2) (truthMultiplicity label 3) := by
  apply truthMultiplicityPattern7_of_sum
  · exact truthMultiplicity_pos label hsurj 0
  · exact truthMultiplicity_pos label hsurj 1
  · exact truthMultiplicity_pos label hsurj 2
  · exact truthMultiplicity_pos label hsurj 3
  · simpa only [Fin.sum_univ_four] using truthMultiplicity_sum label

end Neoplatonic.LTR
