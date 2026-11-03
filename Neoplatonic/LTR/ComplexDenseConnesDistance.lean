import Neoplatonic.LTR.ComplexDenseMarkedCommutatorCriterion

/-!
# Exact Connes-style distance from the genuine complex Hilbert commutator norm

Let X be any metric space with a dense enumerated sequence and
all distinct dense pairs represented among countably many marked
edges, with scale 1 / dist. For continuous real observables having
a finite uniform edge-gradient bound, the norm-one ball of the actual
bounded infinite complex Hilbert commutator gives the original metric.

The distance-to-target observable is a norm-one admissible witness,
so equality is attained. To package a full spectral triple on C(X)
one must also invoke the boundedness of the continuous observable
representation, automatic for compact X but not bundled here.
-/

namespace Neoplatonic.LTR

/-- Exact dual metric formula in terms of the bounded complex Hilbert
commutator extending the maximal-domain unbounded Dirac action. -/
theorem complexDenseConnesDistance_operator_witness
    {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (mass : ℕ → ℝ)
    (hOne : (0 : ℝ) ≤ 1)
    (x y : X) :
    (∀ (a : X → ℝ), Continuous a →
       ∀ (L : ℝ) (hL : 0 ≤ L)
         (hEdge : ∀ j,
           |(dist (left j) (right j))⁻¹ *
              (a (right j) - a (left j))| ≤ L),
       ‖complexPairCommutatorCLM
         mass
         (fun j => (dist (left j) (right j))⁻¹)
         (fun j => a (left j))
         (fun j => a (right j))
         L hL hEdge‖ ≤ 1 →
       |a x - a y| ≤ dist x y) ∧
    ∃ (a : X → ℝ) (ha : Continuous a)
      (hEdge : ∀ j,
        |(dist (left j) (right j))⁻¹ *
          (a (right j) - a (left j))| ≤ 1),
      ‖complexPairCommutatorCLM
        mass
        (fun j => (dist (left j) (right j))⁻¹)
        (fun j => a (left j))
        (fun j => a (right j))
        1 hOne hEdge‖ ≤ 1 ∧
      |a x - a y| = dist x y := by
  obtain ⟨hupper, ⟨a, ha, hedge, heq⟩⟩ :=
    denseMarkedConnesDistance_witness
      q hq left right hdistinct hcover x y
  constructor
  · intro f hf L hL hEdge hnorm
    exact hupper f hf
      ((complexPairCommutator_norm_le_iff
        mass
        (fun j => (dist (left j) (right j))⁻¹)
        (fun j => f (left j))
        (fun j => f (right j))
        L 1 hL hEdge hOne).mp hnorm)
  · refine ⟨a, ha, hedge, ?_, heq⟩
    exact complexPairCommutatorCLM_norm_le
      mass
      (fun j => (dist (left j) (right j))⁻¹)
      (fun j => a (left j))
      (fun j => a (right j))
      1 hOne hedge

end Neoplatonic.LTR
