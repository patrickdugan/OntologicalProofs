import Neoplatonic.LTR.LogicalStoneMarking
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Spectral geometry on the genuine logical completion space

Under a countable sentence language, the completion space
T.CompleteType α is compact, totally separated, second-countable,
and thus metrizable. Urysohn's theorem supplies a compatible
metric. A satisfiable theory with an independent sentence has a
nontrivial classically selected dense sequence of completions.

With the explicit Nat.unpair edge marking, the previously verified
constructor produces a faithful compact complex spectral triple
recovering this chosen compatible metric.

The metric is chosen classically: it is not asserted to be
computable from sentence codes, nor interpretation-invariant.
-/

namespace Neoplatonic.LTR

open FirstOrder Set TopologicalSpace
open FirstOrder.Language.Theory

universe u v w

variable {L : FirstOrder.Language.{u,v}} {T : L.Theory}
variable {α : Type w}

/-- Urysohn metrization provides a metric compatible with the
logical Stone topology on the first-order completion space. -/
noncomputable def chosenLogicalStoneMetric
    [Countable (L.withConstants α).Sentence] :
    MetricSpace (T.CompleteType α) := by
  letI : SecondCountableTopology (T.CompleteType α) :=
    logicalCompleteType_secondCountable (T := T) (α := α)
  letI : TopologicalSpace.MetrizableSpace (T.CompleteType α) :=
    inferInstance
  exact TopologicalSpace.metrizableSpaceMetric _

/-- A full spectral triple for Mathlib's logical completion space,
using its chosen compatible metric and a classically chosen dense
enumeration. An independent sentence provides two distinct points. -/
noncomputable def chosenLogicalStoneSpectralTriple
    [Countable (L.withConstants α).Sentence]
    (hT : T.IsSatisfiable)
    (φ : (L.withConstants α).Sentence)
    (hi : Independent T φ) :
    letI : MetricSpace (T.CompleteType α) :=
      chosenLogicalStoneMetric (T := T) (α := α)
    letI : TopologicalSpace (T.CompleteType α) :=
      TopologicalSpace.generateFrom (Set.range (T.typesWith (α := α)))
    CompactComplexSpectralTriple (T.CompleteType α) := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  letI : TopologicalSpace (T.CompleteType α) :=
    TopologicalSpace.generateFrom (Set.range (T.typesWith (α := α)))
  letI : SecondCountableTopology (T.CompleteType α) :=
    logicalCompleteType_secondCountable (T := T) (α := α)
  letI : Nonempty (T.CompleteType α) :=
    (CompleteType.nonempty_iff).mpr hT
  let q : ℕ → T.CompleteType α :=
    logicalCompleteType_denseSeq (T := T) (α := α) hT
  have hq : DenseRange q :=
    logicalCompleteType_denseSeq_dense (T := T) (α := α) hT
  have htwo : ∃ a b : ℕ, q a ≠ q b :=
    logicalCompleteType_denseSeq_has_distinct (T := T) (α := α) hT φ hi
  let a : ℕ := Classical.choose htwo
  let b : ℕ := Classical.choose (Classical.choose_spec htwo)
  have hab : q a ≠ q b :=
    Classical.choose_spec (Classical.choose_spec htwo)
  exact explicitDensePairSpectralTriple q hq a b hab

end Neoplatonic.LTR
