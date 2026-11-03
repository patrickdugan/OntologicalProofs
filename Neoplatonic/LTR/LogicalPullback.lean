import Neoplatonic.LTR.LogicalSpectral
import Neoplatonic.LTR.NullaryContinuity

/-!
# A commuting square: syntax, complete theories, and operator observables

The actual first-order nullary-language endomorphism associated with a
program e induces a continuous transformation of the Cantor completion
space. Pulling a named clopen truth projection back along this map is
*exactly* the logical projection of the syntactically translated
sentence, for every first-order sentence, including quantified ones.

This is the full continuous-observable functoriality of the labelled
syntax/Stone correspondence. It avoids any claim about canonical
intertwiners of independently chosen infinite Dirac eigenbases.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language

/-- The continuous completion-space action as a genuine continuous map. -/
noncomputable def syntaxMapContinuous (e : Nat.Partrec.Code) :
    C(Nullary.T.CompleteType Empty, Nullary.T.CompleteType Empty) :=
  ⟨Nullary.syntaxMap e, Nullary.continuous_syntaxMap e⟩

/-- Syntactic translation and geometric pullback commute on every
first-order sentence's continuous truth projection. -/
theorem logicalProjection_syntax_pullback
    (e : Nat.Partrec.Code) (φ : Nullary.L.Sentence) :
    (logicalProjection (T := Nullary.T) (Nullary.liftedSentence φ)).comp
        (syntaxMapContinuous e) =
      logicalProjection (T := Nullary.T)
        (Nullary.liftedSentence ((Nullary.haltingRename e).onSentence φ)) := by
  ext p
  change logicalProjection (T := Nullary.T) (Nullary.liftedSentence φ)
      (Nullary.syntaxMap e p) =
    logicalProjection (T := Nullary.T)
      (Nullary.liftedSentence ((Nullary.haltingRename e).onSentence φ)) p
  have hsem := Nullary.syntaxMap_semantics e p φ
  by_cases hp : Nullary.liftedSentence φ ∈ Nullary.syntaxMap e p
  · have hq : Nullary.liftedSentence
        ((Nullary.haltingRename e).onSentence φ) ∈ p := hsem.mp hp
    rw [logicalProjection_apply_mem (T := Nullary.T)
      (Nullary.liftedSentence φ) (Nullary.syntaxMap e p) hp,
      logicalProjection_apply_mem (T := Nullary.T)
      (Nullary.liftedSentence ((Nullary.haltingRename e).onSentence φ)) p hq]
  · have hq : Nullary.liftedSentence
        ((Nullary.haltingRename e).onSentence φ) ∉ p :=
      fun hh => hp (hsem.mpr hh)
    rw [logicalProjection_apply_not_mem (T := Nullary.T)
      (Nullary.liftedSentence φ) (Nullary.syntaxMap e p) hp,
      logicalProjection_apply_not_mem (T := Nullary.T)
      (Nullary.liftedSentence ((Nullary.haltingRename e).onSentence φ)) p hq]

end Neoplatonic.LTR
