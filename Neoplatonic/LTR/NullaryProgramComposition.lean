import Neoplatonic.LTR.NullaryCountableSyntaxMetric

/-!
# Composition of concrete partial-recursive first-order theory maps

Every partial-recursive code e induces a genuine nullary-language
syntactic renaming and an associated complete-theory endomorphism.
The full expanded-sentence semantic identity proves that the
composition of two such maps transports sentence truth via the
reverse composition of the corresponding sentence substitutions.

The fixed classical enumeration of every expanded sentence supplies
the corresponding two index lookups. Their nested finite-prefix
modulus bounds the composed complete-theory map in the exact
sentence-numbered Stone metric.

No hypothesis asserting semantic truth preservation is left
unproved for these concrete nullary-language maps.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- All expanded-language sentence truths for a composition of
two genuine program-induced syntactic endomorphisms. -/
theorem syntaxMap_comp_expanded_semantics
    (e f : Nat.Partrec.Code)
    (p : T.CompleteType Empty)
    (ψ : L[[Empty]].Sentence) :
    ψ ∈ syntaxMap f (syntaxMap e p) ↔
      expandedHaltingRename e (expandedHaltingRename f ψ) ∈ p := by
  exact (syntaxMap_expanded_semantics f (syntaxMap e p) ψ).trans
    (syntaxMap_expanded_semantics e p (expandedHaltingRename f ψ))

/-- The fixed sentence-index lookups obey the exact composite
pullback law on genuine complete first-order theories. -/
theorem nullaryProgram_comp_lookup_truth
    (e f : Nat.Partrec.Code) :
    ∀ j (p : T.CompleteType Empty),
      nullarySentenceCode j ∈ syntaxMap f (syntaxMap e p) ↔
      nullarySentenceCode
        ((nullaryProgramSentenceLookup e ∘
          nullaryProgramSentenceLookup f) j) ∈ p := by
  intro j p
  exact (nullaryProgramSentenceLookup_truth f j (syntaxMap e p)).trans
    (nullaryProgramSentenceLookup_truth e
      (nullaryProgramSentenceLookup f j) p)

/-- An explicit nested prefix bound for any pair of concrete
program-induced logical endomorphisms on the one-axiom theory. -/
theorem nullaryProgram_comp_prefixTransfer
    (e f : Nat.Partrec.Code)
    (n : ℕ) (p q : T.CompleteType Empty)
    (hsource : ∀ i,
      i < sentenceIndexPrefixModulus
        (nullaryProgramSentenceLookup e)
        (sentenceIndexPrefixModulus (nullaryProgramSentenceLookup f) n) →
      (nullarySentenceCode i ∈ p ↔ nullarySentenceCode i ∈ q)) :
    ∀ j, j < n →
      (nullarySentenceCode j ∈ syntaxMap f (syntaxMap e p) ↔
        nullarySentenceCode j ∈ syntaxMap f (syntaxMap e q)) := by
  exact numberedSemanticMap_comp_prefixTransfer
    nullarySentenceCode nullarySentenceCode nullarySentenceCode
    (syntaxMap e) (syntaxMap f)
    (nullaryProgramSentenceLookup e)
    (nullaryProgramSentenceLookup f)
    (nullaryProgramSentenceLookup_truth e)
    (nullaryProgramSentenceLookup_truth f)
    n p q hsource

/-- The genuine composition of two program-induced nullary
theory maps satisfies the explicit nested metric continuity bound. -/
theorem nullaryProgram_comp_radiusTransfer
    (e f : Nat.Partrec.Code)
    (n : ℕ) (p q : T.CompleteType Empty)
    (hnear :
      (letI : MetricSpace (T.CompleteType Empty) :=
        numberedSentenceMetric nullarySentenceCode
          nullarySentenceCode_surjective;
        dist q p) ≤
        (1 / 2 : ℝ)^sentenceIndexPrefixModulus
          (nullaryProgramSentenceLookup e)
          (sentenceIndexPrefixModulus (nullaryProgramSentenceLookup f) n)) :
    (letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric nullarySentenceCode
        nullarySentenceCode_surjective;
      dist (syntaxMap f (syntaxMap e q))
        (syntaxMap f (syntaxMap e p))) ≤
        (1 / 2 : ℝ)^n := by
  exact numberedSemanticMap_comp_radiusTransfer
    nullarySentenceCode nullarySentenceCode nullarySentenceCode
    nullarySentenceCode_surjective
    nullarySentenceCode_surjective
    nullarySentenceCode_surjective
    (syntaxMap e) (syntaxMap f)
    (nullaryProgramSentenceLookup e)
    (nullaryProgramSentenceLookup f)
    (nullaryProgramSentenceLookup_truth e)
    (nullaryProgramSentenceLookup_truth f)
    n p q hnear

end Neoplatonic.LTR.Nullary
