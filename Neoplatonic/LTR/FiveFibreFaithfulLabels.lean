import Neoplatonic.LTR.FiveFibreCanonicalNoGo
import Mathlib.Tactic

/-!
# LTR-MAN-38: classify faithful diagonal truth representations in dimension five

A diagonal representation of the Boolean truth algebra ℂ^4 on ℂ^5
is specified by a truth-label function lab : Fin 5 → Fin 4.
Faithfulness means this label function is surjective.

There are five basis coordinates spread over four nonempty truth
fibres. Exactly one truth fibre must have dimension two; the other
three have dimension one. This result is independent of Dirac
geometry and supplies the multiplicity partition used in the
canonical five-dimensional no-go.

The subsequent representation-theoretic bridge must permute an
arbitrary faithful label function to the canonical doubled-00 chart
and prove Hilbert operator-norm / Connes dual invariance under that
coordinate-basis permutation. Non-diagonal faithful representations
also need unitary simultaneous diagonalization of the four minimal
orthogonal projections.
-/

namespace Neoplatonic.LTR

/-- Cardinality of a truth sector in a five-coordinate diagonal
representation of the four-atom truth algebra. -/
def fiveFibreTruthMultiplicity (label : Fin 5 → Fin 4)
    (v : Fin 4) : ℕ :=
  (Finset.univ.filter (fun i : Fin 5 => label i = v)).card

/-- A faithful diagonal representation has a nonempty fibre over
each atomic truth value. -/
theorem fiveFibreTruthMultiplicity_pos
    (label : Fin 5 → Fin 4)
    (hsurj : Function.Surjective label)
    (v : Fin 4) :
    1 ≤ fiveFibreTruthMultiplicity label v := by
  obtain ⟨i, hi⟩ := hsurj v
  have hmem : i ∈ (Finset.univ.filter
      (fun j : Fin 5 => label j = v)) := by
    simp [hi]
  have hpos : 0 < (Finset.univ.filter
      (fun j : Fin 5 => label j = v)).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  dsimp [fiveFibreTruthMultiplicity]
  omega

/-- Sum of the four atomic multiplicities equals the dimension
of the five-coordinate Hilbert representation. -/
theorem fiveFibreTruthMultiplicity_sum
    (label : Fin 5 → Fin 4) :
    (∑ v : Fin 4, fiveFibreTruthMultiplicity label v) = 5 := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := label) (s := Finset.univ) (t := Finset.univ)
    (by intro i hi; exact Finset.mem_univ _)
  simpa [fiveFibreTruthMultiplicity] using h.symm

/-- Any surjective assignment of five Hilbert basis positions to
four atomic truth values has multiplicity pattern (2,1,1,1),
with the unique two-dimensional fibre identified by its truth label. -/
theorem fiveFibreFaithful_uniqueDouble
    (label : Fin 5 → Fin 4)
    (hsurj : Function.Surjective label) :
    ∃ v : Fin 4,
      fiveFibreTruthMultiplicity label v = 2 ∧
      ∀ w : Fin 4, w ≠ v →
        fiveFibreTruthMultiplicity label w = 1 := by
  have hsum := fiveFibreTruthMultiplicity_sum label
  rw [Fin.sum_univ_four] at hsum
  have h0 := fiveFibreTruthMultiplicity_pos label hsurj (0 : Fin 4)
  have h1 := fiveFibreTruthMultiplicity_pos label hsurj (1 : Fin 4)
  have h2 := fiveFibreTruthMultiplicity_pos label hsurj (2 : Fin 4)
  have h3 := fiveFibreTruthMultiplicity_pos label hsurj (3 : Fin 4)
  have hcase :
      (fiveFibreTruthMultiplicity label 0 = 2 ∧
        fiveFibreTruthMultiplicity label 1 = 1 ∧
        fiveFibreTruthMultiplicity label 2 = 1 ∧
        fiveFibreTruthMultiplicity label 3 = 1) ∨
      (fiveFibreTruthMultiplicity label 0 = 1 ∧
        fiveFibreTruthMultiplicity label 1 = 2 ∧
        fiveFibreTruthMultiplicity label 2 = 1 ∧
        fiveFibreTruthMultiplicity label 3 = 1) ∨
      (fiveFibreTruthMultiplicity label 0 = 1 ∧
        fiveFibreTruthMultiplicity label 1 = 1 ∧
        fiveFibreTruthMultiplicity label 2 = 2 ∧
        fiveFibreTruthMultiplicity label 3 = 1) ∨
      (fiveFibreTruthMultiplicity label 0 = 1 ∧
        fiveFibreTruthMultiplicity label 1 = 1 ∧
        fiveFibreTruthMultiplicity label 2 = 1 ∧
        fiveFibreTruthMultiplicity label 3 = 2) := by
    omega
  rcases hcase with c | c | c | c
  · refine ⟨0, c.1, ?_⟩
    intro w hw
    fin_cases w <;> simp_all
  · refine ⟨1, c.2.1, ?_⟩
    intro w hw
    fin_cases w <;> simp_all
  · refine ⟨2, c.2.2.1, ?_⟩
    intro w hw
    fin_cases w <;> simp_all
  · refine ⟨3, c.2.2.2, ?_⟩
    intro w hw
    fin_cases w <;> simp_all

end Neoplatonic.LTR
