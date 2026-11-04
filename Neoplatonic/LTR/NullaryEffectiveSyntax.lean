import Neoplatonic.LTR.NullaryProgramComposition
import Mathlib.ModelTheory.Encoding

/-!
# Constructive natural-number encoding of the full nullary sentence syntax

Mathlib supplies a verified concrete list encoding/decoder for
first-order terms and bounded formulas. The nullary signature has
empty function sorts, and its relation sorts are natural numbers
at arity zero and empty otherwise.

We install Encodable instances directly from those data (without
a classical countability witness), including a complete encoding
for every expanded-language sentence. Encoding and decoding are
actual total definitions using natural numbers and Option; the
round-trip laws are proved.

The total enumeration returns a fixed valid sentence on invalid
codes. It is surjective. The effective index lookup encodes the
actual recursively defined expandedHaltingRename of the decoded
sentence, and its lookup law is checked.

This proves executable encodings via the Encodable interface.
The stronger Mathlib Primcodable/Primrec classification of
formula substitution is a separate formalization task.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- Every function-symbol sort of the nullary language has a
constructive encoding, since each such sort is Empty. -/
instance nullaryFunctionSymbolsEncodable :
    ∀ n : ℕ, Encodable (L.Functions n) := by
  intro n
  change Encodable Empty
  infer_instance

/-- Every relation-symbol sort has a constructive encoding:
arity zero is Nat and all positive arities are Empty. -/
instance nullaryRelationSymbolsEncodable :
    ∀ n : ℕ, Encodable (L.Relations n) := by
  intro n
  cases n with
  | zero =>
      change Encodable ℕ
      infer_instance
  | succ n =>
      change Encodable Empty
      infer_instance

/-- Constructively encode the dependent sigma type of
function symbols, needed by Mathlib's term encoding. -/
instance nullarySigmaFunctionsEncodable :
    Encodable (Σ n : ℕ, L.Functions n) := inferInstance

/-- Constructively encode the dependent sigma type of
relation symbols, needed by Mathlib's formula encoding. -/
instance nullarySigmaRelationsEncodable :
    Encodable (Σ n : ℕ, L.Relations n) := inferInstance

/-- Constructive encoding for every term over a bounded
variable context in the nullary language. -/
instance nullaryTermsEncodable :
    ∀ k : ℕ, Encodable (L.Term (Empty ⊕ Fin k)) := by
  intro k
  infer_instance

/-- A constructive encoding of all variable-context-indexed terms. -/
instance nullarySigmaTermsEncodable :
    Encodable (Σ k : ℕ, L.Term (Empty ⊕ Fin k)) := inferInstance

/-- The Mathlib bounded-formula list encoding is promoted to a
natural-number encoding by its explicit list decoder. -/
instance nullarySigmaFormulasEncodable :
    Encodable (Σ n : ℕ, L.BoundedFormula Empty n) := by
  let e : Computability.Encoding
      (Σ n : ℕ, L.BoundedFormula Empty n)
      ((Σ k : ℕ, L.Term (Empty ⊕ Fin k)) ⊕
        ((Σ n : ℕ, L.Relations n) ⊕ ℕ)) :=
    FirstOrder.Language.BoundedFormula.encoding
  exact Encodable.ofLeftInjection e.encode e.decode e.decode_encode

/-- Constructive encoding of arbitrary original-language sentences,
including quantified ones. -/
instance nullaryOriginalSentenceEncodable : Encodable L.Sentence := by
  exact Encodable.ofLeftInjection
    (fun φ : L.Sentence => (⟨0, φ⟩ : Σ n : ℕ, L.BoundedFormula Empty n))
    (fun s => match s with
      | ⟨0, φ⟩ => some φ
      | ⟨_ + 1, _⟩ => none)
    (by intro φ; rfl)

/-- Constructive encoding of the *full* empty-constant expanded
sentence type, transported through the verified language equivalence. -/
instance nullaryExpandedSentenceEncodable :
    Encodable L[[Empty]].Sentence :=
  Encodable.ofEquiv L.Sentence emptyConstantSentenceEquiv.symm

/-- Encode any genuine expanded sentence as a natural number. -/
def effectiveExpandedSentenceEncode (ψ : L[[Empty]].Sentence) : ℕ :=
  Encodable.encode ψ

/-- A total partial decoder for genuine expanded-language sentences. -/
def effectiveExpandedSentenceDecode (n : ℕ) :
    Option L[[Empty]].Sentence :=
  Encodable.decode n

/-- The encoder and decoder have an exact round-trip law. -/
theorem effectiveExpandedSentence_decode_encode
    (ψ : L[[Empty]].Sentence) :
    effectiveExpandedSentenceDecode
      (effectiveExpandedSentenceEncode ψ) = some ψ :=
  Encodable.encodek ψ

/-- A total expanded-sentence numbering; invalid codes fall back
to a fixed sentence. This map is executable and surjective. -/
def effectiveExpandedSentenceCode (n : ℕ) : L[[Empty]].Sentence :=
  (effectiveExpandedSentenceDecode n).getD ⊥

/-- Every expanded first-order sentence is produced by the
total, explicit natural-number numbering. -/
theorem effectiveExpandedSentenceCode_surjective :
    Function.Surjective effectiveExpandedSentenceCode := by
  intro ψ
  refine ⟨effectiveExpandedSentenceEncode ψ, ?_⟩
  simp only [effectiveExpandedSentenceCode]
  rw [effectiveExpandedSentence_decode_encode]
  rfl

/-- Direct index lookup: decode the numbered sentence, perform
the genuine finite syntactic substitution, and encode the result. -/
def effectiveHaltingSentenceLookup (e : Nat.Partrec.Code) (j : ℕ) : ℕ :=
  effectiveExpandedSentenceEncode
    (expandedHaltingRename e (effectiveExpandedSentenceCode j))

/-- The lookup's defining equation is a verified exact equality of
actual expanded first-order sentences. -/
theorem effectiveHaltingSentenceLookup_spec
    (e : Nat.Partrec.Code) (j : ℕ) :
    effectiveExpandedSentenceCode (effectiveHaltingSentenceLookup e j) =
      expandedHaltingRename e (effectiveExpandedSentenceCode j) := by
  unfold effectiveHaltingSentenceLookup effectiveExpandedSentenceCode
  rw [effectiveExpandedSentence_decode_encode]
  rfl

/-- Full-sentence semantic pullback with a constructive index
selector instead of a Classical.choose surjection witness. -/
theorem effectiveHaltingSentenceLookup_truth
    (e : Nat.Partrec.Code) :
    ∀ j (p : T.CompleteType Empty),
      effectiveExpandedSentenceCode j ∈ syntaxMap e p ↔
      effectiveExpandedSentenceCode (effectiveHaltingSentenceLookup e j) ∈ p := by
  intro j p
  rw [effectiveHaltingSentenceLookup_spec]
  exact syntaxMap_expanded_semantics e p (effectiveExpandedSentenceCode j)

end Neoplatonic.LTR.Nullary
