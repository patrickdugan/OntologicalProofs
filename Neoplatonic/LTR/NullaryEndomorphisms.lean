import Neoplatonic.LTR.NullaryCompleteness
import Neoplatonic.LTR.HaltingGeometry

/-!
# A halting-hard geometric property of first-order theory endomorphisms

On the classified Boolean completion space, take the map induced
by the actual syntactic predicate renaming. Its semantic action on
every original-language sentence follows from the full-sentence model theorem.

The two-sided encode/decode equivalence transfers an undecidable finite
Lipschitz-bound predicate from Boolean streams to complete theories.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The action of syntactic halting-index renaming on complete theories,
via the proved bijection with Boolean truth assignments. -/
noncomputable def syntaxMap (e : Nat.Partrec.Code) :
    T.CompleteType Empty → T.CompleteType Empty :=
  fun p => encode (acceleratedStream (stagedHalting e) (decode p))

theorem decode_syntaxMap (e : Nat.Partrec.Code)
    (p : T.CompleteType Empty) :
    decode (syntaxMap e p) =
      acceleratedStream (stagedHalting e) (decode p) :=
  decode_encode _

def liftedSentence (φ : L.Sentence) : L[[Empty]].Sentence :=
  (L.lhomWithConstants Empty).onSentence φ

/-- Membership in the explicit complete type matches model satisfaction. -/
theorem liftedSentence_mem_encode_iff (bits : ℕ → Bool) (φ : L.Sentence) :
    liftedSentence φ ∈ encode bits ↔
      @FirstOrder.Language.Sentence.Realize L Unit (unitStructure bits) φ := by
  letI : L.Structure Unit := unitStructure bits
  letI : (constantsOn Empty).Structure Unit :=
    constantsOn.structure (fun e : Empty => (e.elim : Unit))
  letI : L[[Empty]].Structure Unit := expandedUnitStructure bits
  exact (mem_encode_iff bits (liftedSentence φ)).trans
    ((L.lhomWithConstants Empty).realize_onSentence Unit φ)

/-- A real syntactic language map agrees on all original sentences. -/
theorem syntaxMap_semantics (e : Nat.Partrec.Code)
    (p : T.CompleteType Empty) (φ : L.Sentence) :
    liftedSentence φ ∈ syntaxMap e p ↔
      liftedSentence ((haltingRename e).onSentence φ) ∈ p := by
  obtain ⟨bits, rfl⟩ := encode_surjective p
  change liftedSentence φ ∈
      encode (acceleratedStream (stagedHalting e) (decode (encode bits))) ↔
    liftedSentence ((haltingRename e).onSentence φ) ∈ encode bits
  rw [decode_encode, liftedSentence_mem_encode_iff,
    liftedSentence_mem_encode_iff]
  exact (haltingRename_realizes_sentence e bits φ).symm

/-- A metric bound on complete theories is exactly a bound on streams. -/
theorem complete_type_metric_iff_stream_metric (e : Nat.Partrec.Code) :
    (∃ C : ℝ, ∀ p q : T.CompleteType Empty,
        markedDistance decode (syntaxMap e p) (syntaxMap e q) ≤
          C * markedDistance decode p q) ↔
    (∃ C : ℝ, ∀ x y : ℕ → Bool,
        markedDistance (fun b : ℕ → Bool => b)
          (acceleratedStream (stagedHalting e) x)
          (acceleratedStream (stagedHalting e) y) ≤
        C * markedDistance (fun b : ℕ → Bool => b) x y) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x y
    have h := hC (encode x) (encode y)
    simpa [syntaxMap, markedDistance, decode_encode] using h
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro p q
    have h := hC (decode p) (decode q)
    simpa [syntaxMap, markedDistance, decode_encode] using h

/-- No algorithm decides finite Lipschitz regularity of this effective
family of syntactic endomorphisms of a finitely axiomatized theory. -/
theorem complete_type_lipschitz_undecidable :
    ¬ ComputablePred (fun e : Nat.Partrec.Code =>
      ∃ C : ℝ, ∀ p q : T.CompleteType Empty,
        markedDistance decode (syntaxMap e p) (syntaxMap e q) ≤
          C * markedDistance decode p q) := by
  intro hdec
  apply Neoplatonic.LTR.finite_real_lipschitz_undecidable
  apply ComputablePred.of_eq hdec
  intro e
  exact complete_type_metric_iff_stream_metric e

end Neoplatonic.LTR.Nullary
