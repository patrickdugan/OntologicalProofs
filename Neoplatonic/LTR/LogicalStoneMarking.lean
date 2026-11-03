import Neoplatonic.LTR.ComplexSpectralSummability
import Neoplatonic.LTR.Stone
import Mathlib.Topology.Bases

/-!
# A dense marking on Mathlib's actual logical Stone completion spaces

The complete-type space of a theory carries the topology generated
by clopen sentence-truth loci. A countable sentence language therefore
gives an explicit countable topological basis (as an indexed family).

For a satisfiable theory, the resulting second-countable compact
Hausdorff space admits a *classically selected* dense sequence.
An independent sentence supplies two distinct completions, ensuring
a nondegenerate fallback edge for Nat.unpair enumeration.

These are mathematical existence statements. Choosing complete
consistent extensions generally requires more information than a
computable sentence enumeration and need not be algorithmic.
-/

namespace Neoplatonic.LTR

open FirstOrder Set

universe u v w

variable {L : FirstOrder.Language.{u,v}} {T : L.Theory}
variable {α : Type w}

/-- The actual first-order complete-type Stone space is second countable
when the underlying expanded sentence type is countable. -/
theorem logicalCompleteType_secondCountable
    [Countable (L.withConstants α).Sentence] :
    SecondCountableTopology (T.CompleteType α) := by
  have hB : IsTopologicalBasis
      (Set.range (T.typesWith (α := α))) :=
    CompleteType.isTopologicalBasis_range_typesWith
  exact hB.secondCountableTopology (Set.countable_range _)

/-- A satisfiable countable-language theory has a classically chosen
dense sequence of genuine complete types. -/
noncomputable def logicalCompleteType_denseSeq
    [Countable (L.withConstants α).Sentence]
    (hT : T.IsSatisfiable) : ℕ → T.CompleteType α := by
  letI : SecondCountableTopology (T.CompleteType α) :=
    logicalCompleteType_secondCountable
  letI : Nonempty (T.CompleteType α) :=
    (CompleteType.nonempty_iff).mpr hT
  exact TopologicalSpace.denseSeq _

/-- The selected complete-type sequence is dense in the Stone topology. -/
theorem logicalCompleteType_denseSeq_dense
    [Countable (L.withConstants α).Sentence]
    (hT : T.IsSatisfiable) :
    DenseRange (logicalCompleteType_denseSeq hT) := by
  letI : SecondCountableTopology (T.CompleteType α) :=
    logicalCompleteType_secondCountable
  letI : Nonempty (T.CompleteType α) :=
    (CompleteType.nonempty_iff).mpr hT
  exact TopologicalSpace.denseRange_denseSeq _

/-- A nontrivial T1 space with a dense sequence must take at least
two distinct values somewhere in that sequence. -/
theorem denseSequence_contains_distinct_values
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (q : ℕ → X) (hq : DenseRange q)
    (x y : X) (hxy : x ≠ y) :
    ∃ a b : ℕ, q a ≠ q b := by
  by_contra hn
  push_neg at hn
  have hconst : ∀ n : ℕ, q n = q 0 := fun n => hn n 0
  have hrange : Set.range q ⊆ ({q 0} : Set X) := by
    rintro z ⟨n, rfl⟩
    exact Set.mem_singleton_iff.mpr (hconst n)
  have hall : Set.univ ⊆ ({q 0} : Set X) := by
    calc
      Set.univ = closure (Set.range q) := hq.closure_eq.symm
      _ ⊆ closure ({q 0} : Set X) := closure_mono hrange
      _ = {q 0} := isClosed_singleton.closure_eq
  have hx : x = q 0 := Set.mem_singleton_iff.mp (hall (Set.mem_univ x))
  have hy : y = q 0 := Set.mem_singleton_iff.mp (hall (Set.mem_univ y))
  exact hxy (hx.trans hy.symm)

/-- An independent sentence separates two genuine complete types. -/
theorem logicalCompleteType_two_distinct
    (φ : (L.withConstants α).Sentence)
    (hi : Independent T φ) :
    ∃ x y : T.CompleteType α, x ≠ y := by
  obtain ⟨⟨x, hx⟩, hproper⟩ :=
    (independent_iff_nontrivial_locus φ).mp hi
  have hnot : ∃ y : T.CompleteType α, y ∉ T.typesWith φ := by
    by_contra hn
    push_neg at hn
    have hall : T.typesWith φ = Set.univ := by
      ext z
      simp only [Set.mem_univ, iff_true]
      exact hn z
    exact hproper hall
  obtain ⟨y, hy⟩ := hnot
  refine ⟨x, y, ?_⟩
  intro hxy
  subst y
  exact hy hx

/-- In a countable satisfiable theory with an independent sentence,
the classically chosen dense sequence has a nondegenerate pair,
sufficient for explicit index-pair marking. -/
theorem logicalCompleteType_denseSeq_has_distinct
    [Countable (L.withConstants α).Sentence]
    (hT : T.IsSatisfiable)
    (φ : (L.withConstants α).Sentence)
    (hi : Independent T φ) :
    ∃ a b : ℕ,
      logicalCompleteType_denseSeq hT a ≠
        logicalCompleteType_denseSeq hT b := by
  obtain ⟨x,y,hxy⟩ := logicalCompleteType_two_distinct φ hi
  exact denseSequence_contains_distinct_values
    (logicalCompleteType_denseSeq hT)
    (logicalCompleteType_denseSeq_dense hT)
    x y hxy

end Neoplatonic.LTR
