import Neoplatonic.LTR.ComplexMarkedMetric
import Mathlib.Topology.Constructions.SumProd

/-!
# Dense countable marking and exact metric recovery

A compact Stone completion can be uncountable, while its spectral
construction samples a countable dense subset Q. The earlier
all-pairs theorem is therefore upgraded here: test all distinct
pairs of a dense sequence q : ℕ → X, and assume the marked edges
cover those pairs. Continuity extends the unit Lipschitz estimate
from Q×Q to all X×X.

The distance-to-target observable witnesses equality in the dual
distance formula. This is a numerical/metric theorem; the norm
identification with the actual Hilbert commutator is established
separately by the bounded-commutator modules.
-/

namespace Neoplatonic.LTR

/-- A continuous real observable with an L-Lipschitz bound on a
dense countable subset satisfies the same bound globally. -/
theorem continuous_lipschitz_of_dense_sequence
    {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (a : X → ℝ) (ha : Continuous a) (L : ℝ)
    (hQ : ∀ m n, |a (q m) - a (q n)| ≤ L * dist (q m) (q n)) :
    ∀ x y, |a x - a y| ≤ L * dist x y := by
  let S : Set (X × X) :=
    {p | |a p.1 - a p.2| ≤ L * dist p.1 p.2}
  have hleft : Continuous (fun p : X × X => |a p.1 - a p.2|) :=
    ((ha.comp continuous_fst).sub (ha.comp continuous_snd)).abs
  have hright : Continuous (fun p : X × X => L * dist p.1 p.2) :=
    continuous_const.mul continuous_dist
  have hclosed : IsClosed S := by
    exact isClosed_le hleft hright
  have hdprod : DenseRange (Prod.map q q) := hq.prodMap hq
  have hsubset : Set.range (Prod.map q q) ⊆ S := by
    rintro p ⟨⟨m, n⟩, rfl⟩
    exact hQ m n
  have hall : Set.univ ⊆ S := by
    simpa only [hdprod.closure_eq] using
      (closure_minimal hsubset hclosed)
  intro x y
  exact hall (Set.mem_univ (x, y))

/-- For a dense sequence and a marking covering every distinct
pair of dense-sequence values, the unit edge-gradient bound on
a continuous observable equals the full 1-Lipschitz condition. -/
theorem denseMarkedEdgeUnitBound_iff_lipschitz
    {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (a : X → ℝ) (ha : Continuous a) :
    (∀ j, |(dist (left j) (right j))⁻¹ *
      (a (right j) - a (left j))| ≤ 1) ↔
    (∀ x y, |a x - a y| ≤ dist x y) := by
  constructor
  · intro hedge
    have hQ : ∀ m n,
        |a (q m) - a (q n)| ≤ (1 : ℝ) * dist (q m) (q n) := by
      intro m n
      by_cases hmn : q m = q n
      · rw [hmn]
        simp
      · obtain ⟨j, hjl, hjr⟩ := hcover m n hmn
        have hj := (markedEdgeBound_iff
          (left j) (right j) (hdistinct j) a 1).mp (hedge j)
        simpa [hjl, hjr] using hj
    intro x y
    simpa only [one_mul] using
      continuous_lipschitz_of_dense_sequence q hq a ha 1 hQ x y
  · intro hlip j
    apply (markedEdgeBound_iff
      (left j) (right j) (hdistinct j) a 1).mpr
    simpa only [one_mul] using hlip (left j) (right j)

/-- The full distance is recovered from continuous observables whose
gradient is at most one on countably many marked dense pairs. -/
theorem denseMarkedConnesDistance_witness
    {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (x y : X) :
    (∀ a : X → ℝ,
      Continuous a →
      (∀ j, |(dist (left j) (right j))⁻¹ *
        (a (right j) - a (left j))| ≤ 1) →
      |a x - a y| ≤ dist x y) ∧
    ∃ a : X → ℝ,
      Continuous a ∧
      (∀ j, |(dist (left j) (right j))⁻¹ *
        (a (right j) - a (left j))| ≤ 1) ∧
      |a x - a y| = dist x y := by
  constructor
  · intro a ha hedge
    exact ((denseMarkedEdgeUnitBound_iff_lipschitz
      q hq left right hdistinct hcover a ha).mp hedge) x y
  · have hcont : Continuous (fun z : X => dist z y) := by fun_prop
    refine ⟨fun z => dist z y, hcont, ?_, ?_⟩
    · apply (denseMarkedEdgeUnitBound_iff_lipschitz
        q hq left right hdistinct hcover
        (fun z => dist z y) hcont).mpr
      intro p r
      exact abs_dist_sub_le p r y
    · simp only [dist_self, sub_zero, abs_of_nonneg dist_nonneg]

end Neoplatonic.LTR
