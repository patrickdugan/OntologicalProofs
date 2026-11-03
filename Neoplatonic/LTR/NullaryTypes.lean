import Neoplatonic.LTR.Nullary

/-!
# Boolean coordinates in genuine first-order completion spaces

The one-axiom theory T has an explicit complete type for each Boolean
truth assignment. The following extracts nullary truth coordinates from
genuine mathlib CompleteType and proves that the explicit model
construction is injective.

Surjectivity (quantifier elimination for the singleton-domain theory) and
the full topological homeomorphism are separate formal goals.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- Interpret an original nullary sentence in the language with an empty
set of added free-variable constants. -/
def liftedAtom (n : ℕ) : L[[Empty]].Sentence :=
  (L.lhomWithConstants Empty).onSentence (atom n)

/-- Truth of an atomic sentence in the canonical complete type equals
the corresponding bit of the original stream. -/
theorem liftedAtom_mem_encode (bits : ℕ → Bool) (n : ℕ) :
    liftedAtom n ∈ encode bits ↔ bits n = true := by
  letI : L.Structure Unit := unitStructure bits
  letI : Unit ⊨ T := unit_models_T bits
  letI : (constantsOn Empty).Structure Unit :=
    constantsOn.structure (fun e : Empty => (e.elim : Unit))
  letI : L[[Empty]].Structure Unit := inferInstance
  have hmem : liftedAtom n ∈ encode bits ↔ Unit ⊨ liftedAtom n := by
    change liftedAtom n ∈ T.typeOf (fun e : Empty => (e.elim : Unit)) ↔
      Unit ⊨ liftedAtom n
    rw [FirstOrder.Language.Theory.CompleteType.mem_typeOf]
    exact FirstOrder.Language.Formula.realize_equivSentence_symm
      (liftedAtom n) (fun e : Empty => (e.elim : Unit))
  calc
    liftedAtom n ∈ encode bits ↔ Unit ⊨ liftedAtom n := hmem
    _ ↔ Unit ⊨ atom n :=
      (L.lhomWithConstants Empty).realize_onSentence (atom n)
    _ ↔ bits n = true := unit_realizes_atom bits n

/-- Read the truth assignment encoded by a complete type. -/
noncomputable def decode (p : T.CompleteType Empty) : ℕ → Bool :=
  fun n => decide (liftedAtom n ∈ p)

/-- All Boolean assignments are recovered exactly from their first-order
complete types. -/
theorem decode_encode (bits : ℕ → Bool) : decode (encode bits) = bits := by
  classical
  funext n
  cases h : bits n with
  | false =>
      simp [decode, (liftedAtom_mem_encode bits n), h]
  | true =>
      simp [decode, (liftedAtom_mem_encode bits n), h]

/-- In particular the completion space contains an injective copy of
the full Boolean Cantor space. -/
theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := congrArg decode h
  simpa [decode_encode] using hh

end Neoplatonic.LTR.Nullary
