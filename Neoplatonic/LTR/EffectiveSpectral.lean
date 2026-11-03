import Neoplatonic.LTR.LogicalDirac
import Mathlib.Computability.Reduce

/-!
# Effective reconstruction: theoremhood equals an operator norm-zero problem

A sentence code names a concrete idempotent continuous observable on its
actual first-order completion space. The observable has a spectral norm
gap: its sup norm is either 0 or 1.

The geometric decision problem "does the refutation observable have norm
zero?" is *exactly* semantic entailment under the original sentence-code
presentation. If semantic entailment is undecidable for a given theory,
so is this norm-zero problem.

The semantic-undecidability premise is explicit; this module does not
attempt arithmetic diagonalization. For a consistent c.e. extension of Q,
the external standard essential-undecidability theorem discharges it.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language
open Set

universe u v w

variable {L : FirstOrder.Language.{u, v}} {T : L.Theory} {α : Type w}

/-- The refutation projection has a strict 0/1 norm gap, with the 1
branch precisely the failure of consequence. -/
theorem refutation_norm_one_iff_not_entails
    (φ : (L.withConstants α).Sentence) :
    ‖logicalProjection (T := T) φ.not‖ = 1 ↔
      ¬ ((L.lhomWithConstants α).onTheory T ⊨ᵇ φ) := by
  constructor
  · intro hone hentails
    have hz := (refutation_norm_zero_iff_entails (T := T) φ).mpr hentails
    rw [hz] at hone
    norm_num at hone
  · intro hnot
    apply logicalProjection_norm_one_of_nonempty (T := T)
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    apply hnot
    apply (refutation_norm_zero_iff_entails (T := T) φ).mp
    exact (logicalProjection_norm_zero_iff (T := T) φ.not).mpr he

/-- The same-code reduction is an exact equivalence of computability.
The input is a natural number indexing a sentence, and the observable
is the specific projection named by that same sentence. -/
theorem refutation_norm_computable_iff_entailment
    (code : ℕ → (L.withConstants α).Sentence) :
    ComputablePred (fun n =>
      ‖logicalProjection (T := T) (code n).not‖ = 0) ↔
    ComputablePred (fun n =>
      (L.lhomWithConstants α).onTheory T ⊨ᵇ code n) := by
  have heq :
      (fun n => ‖logicalProjection (T := T) (code n).not‖ = 0) =
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n) := by
    funext n
    exact propext (refutation_norm_zero_iff_entails (T := T) (code n))
  rw [heq]

/-- An undecidable theoremhood predicate induces an undecidable
real-valued projection norm-zero predicate on the Stone completion space. -/
theorem refutation_norm_undecidable_of_entailment
    (code : ℕ → (L.withConstants α).Sentence)
    (h : ¬ ComputablePred (fun n =>
      (L.lhomWithConstants α).onTheory T ⊨ᵇ code n)) :
    ¬ ComputablePred (fun n =>
      ‖logicalProjection (T := T) (code n).not‖ = 0) := by
  intro hc
  exact h ((refutation_norm_computable_iff_entailment (T := T) code).mp hc)

end Neoplatonic.LTR
