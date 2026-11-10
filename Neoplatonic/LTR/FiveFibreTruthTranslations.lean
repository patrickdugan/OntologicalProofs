import Neoplatonic.LTR.FiveFibreChartPermutation
import Mathlib.Tactic

/-!
# LTR-MAN-40: move any doubled truth atom to 00 by a square isometry

The four two-bit truth values form a Boolean square. Translation
by one of its vertices in the group (ℤ/2ℤ)^2 is a permutation
of the four vertices preserving their Hamming distances.
We implement the four translations explicitly as disjoint
transpositions on Fin 4, and certify all cases by finite reduction.

For an arbitrary faithful diagonal label : Fin 5 → Fin 4,
MAN-38 identifies the unique truth atom with multiplicity two.
Translation by that atom makes 00 the doubled atom. MAN-39 then
constructs a permutation of the five Hilbert coordinates taking
the translated labeling to the fixed canonical chart.

This is the full finite combinatorial basis-relabeling theorem.
The next obligation is to prove the genuine operator norm and
Connes dual supremum invariant under that basis permutation.
-/

namespace Neoplatonic.LTR

/-- The graph distance on the two-bit Boolean square, with vertices
00=0, 01=1, 10=2, 11=3. -/
def twoBitSquareHamming (u v : Fin 4) : ℕ :=
  if u = v then 0
  else if (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) ∨
      (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) then 2
  else 1

/-- The translations of the two-bit Boolean square. Each map
flips the two coordinates selected by v. -/
def twoBitSquareTranslation (v : Fin 4) : Fin 4 ≃ Fin 4 :=
  if v = 0 then Equiv.refl (Fin 4)
  else if v = 1 then
    (Equiv.swap (0 : Fin 4) 1).trans (Equiv.swap 2 3)
  else if v = 2 then
    (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap 1 3)
  else
    (Equiv.swap (0 : Fin 4) 3).trans (Equiv.swap 1 2)

/-- Translating by v sends that vertex to the origin 00. -/
theorem twoBitSquareTranslation_self_to_zero (v : Fin 4) :
    twoBitSquareTranslation v v = 0 := by
  fin_cases v <;> decide

/-- All four Boolean-square translations preserve exact Hamming
distances on every pair of truth atoms. -/
theorem twoBitSquareTranslation_hamming
    (v u w : Fin 4) :
    twoBitSquareHamming
      (twoBitSquareTranslation v u) (twoBitSquareTranslation v w) =
      twoBitSquareHamming u w := by
  fin_cases v <;> fin_cases u <;> fin_cases w <;> decide

/-- Every faithful diagonal five-coordinate truth representation
is equivalent, by a Boolean-square Hamming isometry and a Hilbert
basis permutation, to the canonical double-00 labeling. -/
theorem fiveFibre_faithful_allLabels_chart
    (label : Fin 5 → Fin 4)
    (hsurj : Function.Surjective label) :
    ∃ (v : Fin 4) (σ : Fin 5 ≃ Fin 5),
      (∀ u w : Fin 4,
        twoBitSquareHamming
          (twoBitSquareTranslation v u)
          (twoBitSquareTranslation v w) =
        twoBitSquareHamming u w) ∧
      (∀ i : Fin 5,
        twoBitSquareTranslation v (label (σ i)) =
          fiveFibreCanonicalLabel i) := by
  obtain ⟨v, hdouble, _⟩ :=
    fiveFibreFaithful_uniqueDouble label hsurj
  let τ := twoBitSquareTranslation v
  let normalized : Fin 5 → Fin 4 := fun i => τ (label i)
  have hsurj' : Function.Surjective normalized := by
    intro w
    obtain ⟨i, hi⟩ := hsurj (τ.symm w)
    refine ⟨i, ?_⟩
    simpa [normalized, hi]
  have hnormDouble :
      fiveFibreTruthMultiplicity normalized 0 = 2 := by
    have hτ : τ v = 0 := twoBitSquareTranslation_self_to_zero v
    have hfilters :
        (Finset.univ.filter fun i : Fin 5 => normalized i = 0) =
        (Finset.univ.filter fun i : Fin 5 => label i = v) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        have heq : τ (label i) = τ v := by
          simpa [normalized, hτ] using h
        exact τ.injective heq
      · intro h
        simp [normalized, h, hτ]
    simpa [fiveFibreTruthMultiplicity, hfilters] using hdouble
  obtain ⟨σ, hσ⟩ :=
    fiveFibre_faithful_doubleZero_chart normalized hsurj' hnormDouble
  refine ⟨v, σ, ?_, ?_⟩
  · exact fun u w => twoBitSquareTranslation_hamming v u w
  · intro i
    exact hσ i

end Neoplatonic.LTR
