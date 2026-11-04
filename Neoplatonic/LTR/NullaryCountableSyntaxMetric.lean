import Neoplatonic.LTR.NullaryConcreteNumberedModulus
import Mathlib.ModelTheory.Encoding

/-!
# An actual sentence enumeration for the one-axiom nullary theory

The language has no function symbols, and its relation symbols
are ℕ in arity zero and empty at all positive arities.
Consequently its full symbol type is countable. Mathlib's
encoding of first-order formulas then proves that the entire
expanded-language sentence type is countable.

A concrete classical enumerator of every expanded-language sentence
is obtained from the general sentence-numbering construction.
It is fed into the already verified explicit halting-index syntax-map
modulus, yielding an unconditional theorem for each program code
relative to the concrete one-axiom theory.

The enumeration is selected by classical choice. Deriving a
computable numbering and computable lookup algorithm is a
separate effective presentation milestone.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The signature of the explicit nullary language is countable. -/
instance nullarySymbolsCountable : Countable L.Symbols := by
  haveI : ∀ n : ℕ, Countable (L.Functions n) := by
    intro n
    change Countable Empty
    infer_instance
  haveI : ∀ n : ℕ, Countable (L.Relations n) := by
    intro n
    cases n with
    | zero =>
        change Countable ℕ
        infer_instance
    | succ n =>
        change Countable Empty
        infer_instance
  infer_instance

/-- All sentences in the empty-constant expansion are countable,
including arbitrary quantified formulas. -/
instance nullaryExpandedSentenceCountable :
    Countable L[[Empty]].Sentence := by
  infer_instance

/-- Classical enumeration of all genuine expanded nullary sentences. -/
noncomputable def nullarySentenceCode : ℕ → L[[Empty]].Sentence :=
  classicalSentenceNumbering (L := L) (α := Empty)

/-- Every genuine expanded first-order sentence occurs in this code. -/
theorem nullarySentenceCode_surjective :
    Function.Surjective nullarySentenceCode :=
  classicalSentenceNumbering_surjective (L := L) (α := Empty)

/-- The index lookup for each actual partial-recursive syntactic
endomorphism on the classically chosen full sentence enumeration. -/
noncomputable def nullaryProgramSentenceLookup
    (e : Nat.Partrec.Code) : ℕ → ℕ :=
  haltingSentenceLookup nullarySentenceCode
    nullarySentenceCode_surjective e

theorem nullaryProgramSentenceLookup_truth
    (e : Nat.Partrec.Code) :
    ∀ j (p : T.CompleteType Empty),
      nullarySentenceCode j ∈ syntaxMap e p ↔
      nullarySentenceCode (nullaryProgramSentenceLookup e j) ∈ p :=
  haltingSentenceLookup_truth nullarySentenceCode
    nullarySentenceCode_surjective e

/-- The concrete one-axiom nullary theory, with the full expanded
sentence-numbered metric, has an explicit prefix-control theorem
for every partial-recursive endomorphism. -/
theorem nullaryProgram_numbered_radiusTransfer
    (e : Nat.Partrec.Code)
    (n : ℕ) (p q : T.CompleteType Empty)
    (hnear :
      (letI : MetricSpace (T.CompleteType Empty) :=
        numberedSentenceMetric nullarySentenceCode
          nullarySentenceCode_surjective;
        dist q p) ≤
          (1 / 2 : ℝ)^sentenceIndexPrefixModulus
            (nullaryProgramSentenceLookup e) n) :
    (letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric nullarySentenceCode
        nullarySentenceCode_surjective;
      dist (syntaxMap e q) (syntaxMap e p)) ≤ (1 / 2 : ℝ)^n := by
  exact syntaxMap_numbered_radiusTransfer
    nullarySentenceCode nullarySentenceCode_surjective
    e n p q hnear

/-- Uniform continuity of every genuine nullary syntactic endomorphism
in the one-axiom theory's own complete sentence-numbered metric. -/
theorem nullaryProgram_numbered_uniformModulus
    (e : Nat.Partrec.Code) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p q : T.CompleteType Empty,
      (letI : MetricSpace (T.CompleteType Empty) :=
        numberedSentenceMetric nullarySentenceCode
          nullarySentenceCode_surjective;
        dist q p) < δ →
      (letI : MetricSpace (T.CompleteType Empty) :=
        numberedSentenceMetric nullarySentenceCode
          nullarySentenceCode_surjective;
        dist (syntaxMap e q) (syntaxMap e p)) < ε := by
  exact syntaxMap_numbered_uniformModulus
    nullarySentenceCode nullarySentenceCode_surjective e ε hε

end Neoplatonic.LTR.Nullary
