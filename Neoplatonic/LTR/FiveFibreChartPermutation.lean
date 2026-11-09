import Neoplatonic.LTR.FiveFibreFaithfulLabels
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# LTR-MAN-39: faithful diagonal chart permutations

A diagonal representation of the Boolean truth algebra on five Hilbert
coordinates is represented by a surjective label : Fin 5 → Fin 4.

Any two labelings with equal cardinalities at each truth atom differ by
a permutation of their five coordinates. The proof uses Mathlib's
fiberwise equivalence and finite subtype cardinalities.

In particular, when the doubled truth fibre has label 00, a Hilbert
coordinate permutation reduces the representation to the canonical
label list (00, 01, 10, 11, 00) used in MAN-37.

The further step is to use Boolean-square isometries to move the
doubled fibre of an arbitrary faithful labeling to 00, and to
transport the matrix Dirac norm across the coordinate permutation.
-/

namespace Neoplatonic.LTR

/-- Truth label of each Hilbert basis coordinate in the canonical
five-dimensional representation: 00 appears twice. -/
def fiveFibreCanonicalLabel (i : Fin 5) : Fin 4 :=
  if i = 0 ∨ i = 4 then 0
  else if i = 1 then 1
  else if i = 2 then 2
  else 3

/-- The canonical chart has exactly two copies of 00 and one
copy of each other Boolean truth atom. -/
theorem fiveFibreCanonicalLabel_multiplicity (v : Fin 4) :
    fiveFibreTruthMultiplicity fiveFibreCanonicalLabel v =
      if v = 0 then 2 else 1 := by
  fin_cases v <;> decide

/-- Same truth-fibre cardinalities give an exact permutation
of the underlying five Hilbert coordinates. -/
theorem fiveFibre_equalMultiplicities_permutation
    (label₁ label₂ : Fin 5 → Fin 4)
    (hcard : ∀ v : Fin 4,
      fiveFibreTruthMultiplicity label₁ v =
      fiveFibreTruthMultiplicity label₂ v) :
    ∃ σ : Fin 5 ≃ Fin 5,
      ∀ i : Fin 5, label₂ (σ i) = label₁ i := by
  classical
  let e : ∀ v : Fin 4,
      {i : Fin 5 // label₁ i = v} ≃
      {j : Fin 5 // label₂ j = v} := fun v =>
    Fintype.equivOfCardEq (by
      simpa only [Fintype.card_subtype,
        fiveFibreTruthMultiplicity] using hcard v)
  exact ⟨Equiv.ofFiberEquiv e, fun i =>
    Equiv.ofFiberEquiv_map e i⟩

/-- If 00 is the doubled atom of a faithful diagonal
representation, permuting its Hilbert coordinates gives the
canonical chart exactly. -/
theorem fiveFibre_faithful_doubleZero_chart
    (label : Fin 5 → Fin 4)
    (hsurj : Function.Surjective label)
    (hdouble : fiveFibreTruthMultiplicity label 0 = 2) :
    ∃ σ : Fin 5 ≃ Fin 5,
      ∀ i : Fin 5, label (σ i) = fiveFibreCanonicalLabel i := by
  obtain ⟨v, hv, hvother⟩ :=
    fiveFibreFaithful_uniqueDouble label hsurj
  have hvzero : v = 0 := by
    by_contra hn
    have h := hvother 0 (Ne.symm hn)
    omega
  subst v
  apply fiveFibre_equalMultiplicities_permutation
    fiveFibreCanonicalLabel label
  intro w
  rw [fiveFibreCanonicalLabel_multiplicity]
  by_cases hw : w = 0
  · subst w
    simpa using hdouble.symm
  · simp only [if_neg hw]
    exact (hvother w hw).symm

end Neoplatonic.LTR
