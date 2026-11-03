import Neoplatonic.LTR.LogicalSpectral

/-!
# Two-point Dirac blocks detect logical disagreements

The already checked real symmetric two-point Dirac block is paired with
the genuine continuous characteristic projection of a first-order
sentence. A nonzero off-diagonal scale makes the commutator vanish
exactly when the two complete theories agree on the sentence.

The block norm, energy, and square identities are covered by
SpectralBridge.lean. The statement here is exact algebraic recognition
of a labelled logical distinction by a finite Dirac commutator.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language

universe u v w
variable {L : FirstOrder.Language.{u, v}} {T : L.Theory} {α : Type w}

/-- With nonzero Dirac coupling, commuting with a diagonal scalar
observable means that its two values coincide. -/
theorem massDirac_commutator_zero_iff_eq
    (mass scale a b : ℝ) (hs : scale ≠ 0) :
    massDirac mass scale * diagonalObservable a b -
       diagonalObservable a b * massDirac mass scale = 0 ↔ a = b := by
  rw [massDirac_commutator]
  constructor
  · intro h
    have hc : scale * (b - a) = 0 := by
      have hentry := congrArg
        (fun m : Matrix (Fin 2) (Fin 2) ℝ => m 0 1) h
      simpa using hentry
    have hab : b - a = 0 := (mul_eq_zero.mp hc).resolve_left hs
    exact (sub_eq_zero.mp hab).symm
  · intro h
    subst b
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- Equal values of a sentence's projection mean equal truth assignments
to that sentence in the two complete theories. -/
theorem logicalProjection_values_eq_iff
    (φ : (L.withConstants α).Sentence) (p q : T.CompleteType α) :
    logicalProjection φ p = logicalProjection φ q ↔
      (φ ∈ p ↔ φ ∈ q) := by
  by_cases hp : φ ∈ p <;> by_cases hq : φ ∈ q <;>
    simp [logicalProjection_apply_mem, logicalProjection_apply_not_mem, hp, hq]

/-- Concrete Dirac commutator is zero exactly when the two
first-order complete theories agree about the chosen sentence. -/
theorem logicalDirac_commutator_zero_iff
    (φ : (L.withConstants α).Sentence)
    (p q : T.CompleteType α)
    (mass scale : ℝ) (hs : scale ≠ 0) :
    massDirac mass scale *
        diagonalObservable (logicalProjection φ p) (logicalProjection φ q) -
      diagonalObservable (logicalProjection φ p) (logicalProjection φ q) *
        massDirac mass scale = 0 ↔
      (φ ∈ p ↔ φ ∈ q) := by
  rw [massDirac_commutator_zero_iff_eq mass scale
    (logicalProjection φ p) (logicalProjection φ q) hs]
  exact logicalProjection_values_eq_iff φ p q

end Neoplatonic.LTR
