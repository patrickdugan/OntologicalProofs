import Neoplatonic.LTR.DepthProfile
import Neoplatonic.LTR.Stone
import Neoplatonic.LTR.Network

/-!
# Truth-preserving maps between actual first-order completion spaces

This interface connects LTR's abstract marked spaces to mathlib's genuine
first-order CompleteType. It represents an interpretation by the induced
map on complete theories and its contravariant sentence translation.
Preservation of membership is part of the interface and must be proved
when constructing a particular syntactic first-order interpretation.

The interface is semantic. It does not assert that every such map is
induced by a computable or first-order definable interpretation.
-/

namespace Neoplatonic.LTR

open FirstOrder Set

universe u v w

/-- A semantic translation from the theory T into S.
Its sentence action is contravariant: S-sentences are expressed in T. -/
structure SentenceTranslation
    {L : FirstOrder.Language.{u, v}} (T S : L.Theory)
    (α : Type w) where
  onType : T.CompleteType α → S.CompleteType α
  onSentence : (L.withConstants α).Sentence → (L.withConstants α).Sentence
  preserves : ∀ (p : T.CompleteType α) (φ : (L.withConstants α).Sentence),
    φ ∈ onType p ↔ onSentence φ ∈ p

namespace SentenceTranslation

variable {L : FirstOrder.Language.{u, v}}
variable {T S R : L.Theory} {α : Type w}

/-- The identity on actual complete theories. -/
def refl (T : L.Theory) (α : Type w) : SentenceTranslation T T α where
  onType := id
  onSentence := id
  preserves := by intros; rfl

/-- Translations compose with sentence translations in reverse order. -/
def comp (j : SentenceTranslation S R α)
    (i : SentenceTranslation T S α) : SentenceTranslation T R α where
  onType := j.onType ∘ i.onType
  onSentence := i.onSentence ∘ j.onSentence
  preserves := by
    intro p φ
    exact (j.preserves (i.onType p) φ).trans (i.preserves p (j.onSentence φ))

/-- Every translated sentence has exactly the expected clopen preimage. -/
theorem preimage_locus (i : SentenceTranslation T S α)
    (φ : (L.withConstants α).Sentence) :
    i.onType ⁻¹' S.typesWith φ =
      T.typesWith (i.onSentence φ) := by
  ext p
  change φ ∈ i.onType p ↔ i.onSentence φ ∈ p
  exact i.preserves p φ

/-- A surjective interpretation is conservative for sentence entailment. -/
theorem entailment_iff_of_surjective (i : SentenceTranslation T S α)
    (hi : Function.Surjective i.onType)
    (φ : (L.withConstants α).Sentence) :
    ((L.lhomWithConstants α).onTheory S ⊨ᵇ φ) ↔
      ((L.lhomWithConstants α).onTheory T ⊨ᵇ i.onSentence φ) := by
  rw [← locus_eq_univ (T := S) φ, ← locus_eq_univ (T := T) (i.onSentence φ)]
  rw [← i.preimage_locus φ]
  exact (cover_pullback_iff i.onType hi (S.typesWith φ)).symm

/-- A surjective interpretation preserves sentence independence. -/
theorem independent_iff_of_surjective (i : SentenceTranslation T S α)
    (hi : Function.Surjective i.onType)
    (φ : (L.withConstants α).Sentence) :
    Independent S φ ↔ Independent T (i.onSentence φ) := by
  rw [independent_iff_nontrivial_locus, independent_iff_nontrivial_locus]
  rw [← i.preimage_locus φ]
  have h := (nontrivial_pullback_iff i.onType hi (S.typesWith φ)).symm
  simpa only [Set.nonempty_iff_ne_empty] using h

end SentenceTranslation

/-- A truth-value marking indexed by a chosen enumeration of sentences. -/
noncomputable def sentenceMark
    {L : FirstOrder.Language.{u, v}} {T : L.Theory}
    {α : Type w} (code : ℕ → (L.withConstants α).Sentence)
    (p : T.CompleteType α) (n : ℕ) : Bool := by
  classical
  exact decide (code n ∈ p)

/-- A syntactic index map is compatible with semantic marks when the
translations of all selected target sentences match source labels. -/
theorem sentenceMark_of_translation
    {L : FirstOrder.Language.{u, v}} {T S : L.Theory}
    {α : Type w}
    (i : SentenceTranslation T S α)
    (ct cs : ℕ → (L.withConstants α).Sentence)
    (index : ℕ → ℕ)
    (hcode : ∀ n, i.onSentence (ct n) = cs (index n))
    (p : T.CompleteType α) (n : ℕ) :
    sentenceMark ct (i.onType p) n = sentenceMark cs p (index n) := by
  classical
  have hiff : (ct n ∈ i.onType p) ↔ (cs (index n) ∈ p) := by
    rw [i.preserves p (ct n), hcode n]
  have heq : (ct n ∈ i.onType p) = (cs (index n) ∈ p) := propext hiff
  simp only [sentenceMark]
  rw [heq]

/-- A bounded index shift supplies the filtration delay, hence the exact
2^c metric and observable bounds from the earlier Lean reconstruction. -/
theorem sentenceTranslation_delay
    {L : FirstOrder.Language.{u, v}} {T S : L.Theory}
    {α : Type w}
    (i : SentenceTranslation T S α)
    (ct cs : ℕ → (L.withConstants α).Sentence)
    (index : ℕ → ℕ) (c : ℕ)
    (hcode : ∀ n, i.onSentence (ct n) = cs (index n))
    (hbound : ∀ n, index n ≤ n + c) :
    TranslationDelay (sentenceMark cs) (sentenceMark ct) i.onType c := by
  intro n x y hxy k hk
  have hindex : index k < n + c :=
    lt_of_le_of_lt (hbound k) (Nat.add_lt_add_right hk c)
  calc
    sentenceMark ct (i.onType x) k =
        sentenceMark cs x (index k) :=
      sentenceMark_of_translation i ct cs index hcode x k
    _ = sentenceMark cs y (index k) := hxy (index k) hindex
    _ = sentenceMark ct (i.onType y) k :=
      (sentenceMark_of_translation i ct cs index hcode y k).symm

/-- Concrete first-order interface to the quantitative theorem. -/
theorem sentenceTranslation_distortion
    {L : FirstOrder.Language.{u, v}} {T S : L.Theory}
    {α : Type w}
    (i : SentenceTranslation T S α)
    (ct cs : ℕ → (L.withConstants α).Sentence)
    (index : ℕ → ℕ) (c : ℕ)
    (hcode : ∀ n, i.onSentence (ct n) = cs (index n))
    (hbound : ∀ n, index n ≤ n + c)
    (x y : T.CompleteType α) :
    markedDistance (sentenceMark ct) (i.onType x) (i.onType y) ≤
      (2 : ℝ)^c * markedDistance (sentenceMark cs) x y :=
  markedDistance_le_of_delay
    (sentenceTranslation_delay i ct cs index c hcode hbound) x y

end Neoplatonic.LTR
