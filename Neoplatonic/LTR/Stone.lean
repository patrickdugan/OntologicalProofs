import Mathlib

/-!
# LTR-01: labelled completion spaces

This file uses mathlib's actual first-order complete types, rather than an
axiomatized surrogate for a logical theory. With `α = Empty`, these are
completions in the harmless empty-constant expansion of the language.

`⊨ᵇ` below is semantic entailment. A syntactic provability predicate is
connected only through the explicit adequacy hypothesis in the last theorem.
Gödel/Rosser incompleteness and the construction of an arithmetic coding are
NOT proved here. The computability statements use `ComputablePred`, not
classical `DecidablePred`.
-/

namespace Neoplatonic.LTR

open FirstOrder Set

universe u v w

variable {L : FirstOrder.Language.{u, v}} {T : L.Theory} {α : Type w}

/-- A sentence is independent when neither it nor its negation is entailed. -/
def Independent (T : L.Theory) (φ : (L.withConstants α).Sentence) : Prop :=
  ¬ ((L.lhomWithConstants α).onTheory T ⊨ᵇ φ) ∧
  ¬ ((L.lhomWithConstants α).onTheory T ⊨ᵇ φ.not)

/-- A sentence's truth locus is genuinely clopen in the completion topology. -/
theorem locus_isClopen (φ : (L.withConstants α).Sentence) :
    IsClopen (T.typesWith φ) :=
  _root_.CompleteType.isClopen_typesWith φ

/-- Entailment is exactly coverage of the labelled completion space. -/
theorem locus_eq_univ (φ : (L.withConstants α).Sentence) :
    T.typesWith φ = Set.univ ↔
      (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  exact FirstOrder.Language.Theory.CompleteType.setOf_mem_eq_univ_iff φ

/-- Logical negation becomes set complement. -/
theorem locus_not (φ : (L.withConstants α).Sentence) :
    T.typesWith φ.not = (T.typesWith φ)ᶜ := by
  ext p
  exact p.not_mem_iff φ

/-- Refutation is exactly emptiness of the labelled locus. -/
theorem locus_eq_empty (φ : (L.withConstants α).Sentence) :
    T.typesWith φ = ∅ ↔
      (L.lhomWithConstants α).onTheory T ⊨ᵇ φ.not := by
  rw [← locus_eq_univ (T := T) φ.not, locus_not]
  simp

/-- Independence is a proper, nonempty clopen split. -/
theorem independent_iff_nontrivial_locus
    (φ : (L.withConstants α).Sentence) :
    Independent T φ ↔
      (T.typesWith φ).Nonempty ∧ T.typesWith φ ≠ Set.univ := by
  unfold Independent
  rw [← locus_eq_univ (T := T) φ, ← locus_eq_empty (T := T) φ]
  rw [Set.nonempty_iff_ne_empty]
  exact and_comm

/-- Export the topological split while retaining the sentence label. -/
theorem independent_gives_clopen_split
    (φ : (L.withConstants α).Sentence) (h : Independent T φ) :
    IsClopen (T.typesWith φ) ∧ (T.typesWith φ).Nonempty ∧
      T.typesWith φ ≠ Set.univ :=
  ⟨locus_isClopen φ, (independent_iff_nontrivial_locus φ).mp h⟩

/-- Equality of labelled loci recovers agreement at all completions. -/
theorem labelled_locus_reconstruction
    (φ ψ : (L.withConstants α).Sentence) :
    T.typesWith φ = T.typesWith ψ ↔
      ∀ p : T.CompleteType α, φ ∈ p ↔ ψ ∈ p := by
  constructor
  · intro h p
    change p ∈ T.typesWith φ ↔ p ∈ T.typesWith ψ
    rw [h]
  · intro h
    ext p
    exact h p

/-- Same-code many-one reduction: the input is a sentence code on both sides.
The coding is part of the presentation. No computable map to arbitrary subsets
or to completed truth assignments is being asserted. -/
theorem entailment_reduces_to_cover
    (code : ℕ → (L.withConstants α).Sentence) :
    ManyOneReducible
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n)
      (fun n => T.typesWith (code n) = Set.univ) := by
  refine ⟨id, Computable.id, ?_⟩
  intro n
  exact (locus_eq_univ (T := T) (code n)).symm

/-- Coverage has exactly the computability of entailment in the same coding. -/
theorem cover_computable_iff
    (code : ℕ → (L.withConstants α).Sentence) :
    ComputablePred (fun n => T.typesWith (code n) = Set.univ) ↔
    ComputablePred (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n) := by
  have h : (fun n => T.typesWith (code n) = Set.univ) =
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n) := by
    funext n
    exact propext (locus_eq_univ (T := T) (code n))
  rw [h]

/-- The undecidability input is an explicit hypothesis, not a hidden axiom. -/
theorem noncomputable_cover_of_noncomputable_entailment
    (code : ℕ → (L.withConstants α).Sentence)
    (h : ¬ ComputablePred
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n)) :
    ¬ ComputablePred (fun n => T.typesWith (code n) = Set.univ) := by
  intro hc
  exact h ((cover_computable_iff code).mp hc)

/-- Adapter for an independently formalized sound and complete proof calculus.
Both adequacy and syntactic undecidability remain visible premises. -/
theorem noncomputable_cover_of_provability
    (code : ℕ → (L.withConstants α).Sentence) (Provable : ℕ → Prop)
    (adequate : ∀ n,
      Provable n ↔ (L.lhomWithConstants α).onTheory T ⊨ᵇ code n)
    (h : ¬ ComputablePred Provable) :
    ¬ ComputablePred (fun n => T.typesWith (code n) = Set.univ) := by
  apply noncomputable_cover_of_noncomputable_entailment code
  intro he
  have hp : Provable =
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n) := by
    funext n
    exact propext (adequate n)
  apply h
  rw [hp]
  exact he

end Neoplatonic.LTR
