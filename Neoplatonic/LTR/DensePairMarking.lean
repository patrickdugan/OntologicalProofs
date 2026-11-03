import Neoplatonic.LTR.ComplexMetricSpectralTriple
import Mathlib.Data.Nat.Pairing

/-!
# Explicit dense-pair edge enumeration

Given q : ℕ → X and two indices a,b with q a ≠ q b,
use Nat.unpair to enumerate all ordered index pairs. For an index
pair with equal q-values, use (a,b) as a fixed nondegenerate edge.

This supplies a total, individually nondegenerate marking that
covers every ordered distinct pair of dense-sequence values and
also covers every value q n as a marked endpoint.

The index arithmetic is computable. Selecting the completion
values q n can be noncomputable; this lemma makes no effective
selection claim about q.
-/

namespace Neoplatonic.LTR

/-- Left endpoint of the marked ordered pair at natural index j. -/
def densePairLeft {X : Type*} (q : ℕ → X)
    (a b : ℕ) (j : ℕ) : X :=
  if q (Nat.unpair j).1 = q (Nat.unpair j).2 then q a
  else q (Nat.unpair j).1

/-- Right endpoint of the marked ordered pair at natural index j. -/
def densePairRight {X : Type*} (q : ℕ → X)
    (a b : ℕ) (j : ℕ) : X :=
  if q (Nat.unpair j).1 = q (Nat.unpair j).2 then q b
  else q (Nat.unpair j).2

/-- Each edge is nondegenerate provided the fallback pair is. -/
theorem densePair_distinct {X : Type*}
    (q : ℕ → X) (a b : ℕ) (hab : q a ≠ q b) :
    ∀ j, densePairLeft q a b j ≠ densePairRight q a b j := by
  intro j
  by_cases h : q (Nat.unpair j).1 = q (Nat.unpair j).2
  · simpa [densePairLeft, densePairRight, h] using hab
  · simpa [densePairLeft, densePairRight, h] using h

/-- Every ordered pair of distinct dense-sequence values appears
at the explicit index Nat.pair m n. -/
theorem densePair_covers {X : Type*}
    (q : ℕ → X) (a b : ℕ) :
    ∀ m n, q m ≠ q n →
      ∃ j, densePairLeft q a b j = q m ∧
        densePairRight q a b j = q n := by
  intro m n hmn
  refine ⟨Nat.pair m n, ?_, ?_⟩
  · simp [densePairLeft, Nat.unpair_pair, hmn]
  · simp [densePairRight, Nat.unpair_pair, hmn]

/-- The marked endpoint list also covers every value of q,
including when q has repeated values. -/
theorem densePair_endpointCover {X : Type*}
    (q : ℕ → X) (a b : ℕ) (hab : q a ≠ q b) :
    ∀ n, ∃ j, densePairLeft q a b j = q n ∨
      densePairRight q a b j = q n := by
  intro n
  by_cases hna : q n = q a
  · refine ⟨Nat.pair a b, Or.inl ?_⟩
    simp [densePairLeft, Nat.unpair_pair, hab, hna]
  · refine ⟨Nat.pair n a, Or.inl ?_⟩
    simp [densePairLeft, Nat.unpair_pair, hna]

/-- For any compact metric space with a dense enumeration containing
two distinct points, the explicit marking constructs a faithful
compact-resolvent complex spectral triple. -/
noncomputable def explicitDensePairSpectralTriple
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (a b : ℕ) (hab : q a ≠ q b) :
    CompactComplexSpectralTriple X :=
  compactComplexMarkedSpectralTriple q hq
    (densePairLeft q a b) (densePairRight q a b)
    (densePair_distinct q a b hab)
    (densePair_endpointCover q a b hab)

/-- The explicit marking has exact Connes-style metric recovery on
every pair of points, using the constructed spectral triple. -/
theorem explicitDensePairSpectralTriple_metric_recovery
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (a b : ℕ) (hab : q a ≠ q b)
    (x y : X) :
    (∀ (f : C(X, ℂ)),
       f ∈ (explicitDensePairSpectralTriple q hq a b hab).observables →
       ∀ (L : ℝ) (hL : 0 ≤ L)
         (hEdge : ∀ j,
           |(dist (densePairLeft q a b j) (densePairRight q a b j))⁻¹| *
             ‖f (densePairRight q a b j) - f (densePairLeft q a b j)‖ ≤ L),
       ‖complexValuedPairCommutatorCLM
         (fun j => (2 : ℝ)^j)
         (fun j => (dist (densePairLeft q a b j) (densePairRight q a b j))⁻¹)
         (fun j => f (densePairLeft q a b j))
         (fun j => f (densePairRight q a b j))
         L hL hEdge‖ ≤ 1 →
       ‖f x - f y‖ ≤ dist x y) ∧
    ∃ (f : C(X, ℂ)),
      f ∈ (explicitDensePairSpectralTriple q hq a b hab).observables ∧
      ∃ (hEdge : ∀ j,
        |(dist (densePairLeft q a b j) (densePairRight q a b j))⁻¹| *
          ‖f (densePairRight q a b j) - f (densePairLeft q a b j)‖ ≤ 1),
        ‖complexValuedPairCommutatorCLM
          (fun j => (2 : ℝ)^j)
          (fun j => (dist (densePairLeft q a b j) (densePairRight q a b j))⁻¹)
          (fun j => f (densePairLeft q a b j))
          (fun j => f (densePairRight q a b j))
          1 (by norm_num) hEdge‖ ≤ 1 ∧
        ‖f x - f y‖ = dist x y := by
  exact compactComplexMarkedSpectralTriple_metric_recovery
    q hq (densePairLeft q a b) (densePairRight q a b)
    (densePair_distinct q a b hab)
    (densePair_endpointCover q a b hab)
    (densePair_covers q a b) x y

end Neoplatonic.LTR
