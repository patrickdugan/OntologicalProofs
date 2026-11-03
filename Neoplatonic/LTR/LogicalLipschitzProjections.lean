import Neoplatonic.LTR.LogicalStoneSpectralTriple
import Neoplatonic.LTR.ComplexLogicalSpectral
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Sentence-labelled clopens are bounded-commutator observables

An indicator of a clopen set in a compact metric space is Lipschitz:
the clopen set and its closed complement have positive uniform
separation. A complex-valued function that takes value one on the
clopen and zero off it has a finite global Lipschitz constant.

Consequently, every first-order sentence's complex Stone truth
projection is an element of the dense Lipschitz star subalgebra for
the selected compatible metric. The genuine infinite-dimensional
spectral triple therefore assigns a bounded Dirac commutator to
every named sentence projection.

This uses a classical compatible metric, and the gradient bound
depends on that metric and on the sentence.
-/

namespace Neoplatonic.LTR

open FirstOrder Set
open FirstOrder.Language.Theory

/-- A binary-valued continuous observable of a compact clopen
set has a finite global complex Lipschitz constant. -/
theorem compactClopenBinary_finiteLipschitz
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (U : Set X) (hU : IsClopen U)
    (f : C(X, ℂ))
    (hone : ∀ x ∈ U, f x = 1)
    (hzero : ∀ x ∉ U, f x = 0) :
    HasFiniteComplexLipschitzConstant f := by
  obtain ⟨r, hr, hgap⟩ :=
    Metric.exists_pos_forall_lt_edist
      hU.isClosed.isCompact hU.compl.isClosed disjoint_compl_right
  have hrreal : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hcross : ∀ x y : X, x ∈ U → y ∉ U →
      (1 : ℝ) ≤ (r : ℝ)⁻¹ * dist x y := by
    intro x y hx hy
    have hn : r ≤ nndist x y := by
      apply ENNReal.coe_le_coe.mp
      simpa only [edist_nndist] using (hgap x hx y hy).le
    have hd : (r : ℝ) ≤ dist x y := by
      exact_mod_cast hn
    calc
      (1 : ℝ) = (r : ℝ)⁻¹ * (r : ℝ) := by
        field_simp
      _ ≤ (r : ℝ)⁻¹ * dist x y :=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hrreal.le)
  refine ⟨(r : ℝ)⁻¹, inv_nonneg.mpr hrreal.le, ?_⟩
  intro x y
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · simp [hone x hx, hone y hy, mul_nonneg,
        inv_nonneg.mpr hrreal.le, dist_nonneg]
    · simpa [hone x hx, hzero y hy] using hcross x y hx hy
  · by_cases hy : y ∈ U
    · simpa [hzero x hx, hone y hy, dist_comm] using
        hcross y x hy hx
    · simp [hzero x hx, hzero y hy, mul_nonneg,
        inv_nonneg.mpr hrreal.le, dist_nonneg]

/-- Every complex sentence-truth projection is Lipschitz with
respect to the classically chosen compatible Stone metric. -/
theorem complexLogicalProjection_mem_Lipschitz
    {L : FirstOrder.Language} {T : L.Theory}
    {α : Type*} [Countable (L.withConstants α).Sentence]
    (φ : (L.withConstants α).Sentence) :
    letI : MetricSpace (T.CompleteType α) :=
      chosenLogicalStoneMetric (T := T) (α := α)
    complexLogicalProjection (T := T) φ ∈
      compactComplexLipschitzStarSubalgebra (T.CompleteType α) := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  change HasFiniteComplexLipschitzConstant
    (complexLogicalProjection (T := T) φ)
  exact compactClopenBinary_finiteLipschitz
    (T.typesWith φ) (locus_isClopen (T := T) (α := α) φ)
    (complexLogicalProjection (T := T) φ)
    (fun p hp => complexLogicalProjection_apply_mem
      (T := T) φ p hp)
    (fun p hp => complexLogicalProjection_apply_not_mem
      (T := T) φ p hp)

end Neoplatonic.LTR
