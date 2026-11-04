import Neoplatonic.LTR.NullaryEffectiveMarkedTriple

/-!
# Exact Connes-style metric recovery for the concrete coded theory

The selected marking of the constructively sentence-numbered nullary
spectral triple covers all distinct ordered pairs of a dense sequence
of genuine complete first-order theories. The bounded commutator of
the infinite maximal-domain complex Hilbert Dirac thus recovers the
first-disagreement Stone metric by duality.

For any two complete theories p,q, every admissible observable whose
actual marked commutator has norm at most 1 separates p and q by at
most their numbered distance. There exists an admissible observable
attaining that distance with commutator norm at most 1.

The sentence code is constructive. The selected dense completion
sequence, and hence the Dirac block endpoints, remain classical.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The actual named nullary syntax-numbered spectral triple recovers
the exact first-disagreement distance from its infinite-Hilbert
bounded Dirac commutator norm, with an attaining observable. -/
theorem effectiveNullaryStoneSpectralTriple_metric_recovery
    (x y : T.CompleteType Empty) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    (∀ (f : C(T.CompleteType Empty, ℂ)),
       f ∈ effectiveNullaryStoneSpectralTriple.observables →
       ∀ (L : ℝ) (hL : 0 ≤ L)
         (hEdge : ∀ j,
           |(dist (effectiveNullaryMarkedLeft j)
               (effectiveNullaryMarkedRight j))⁻¹| *
             ‖f (effectiveNullaryMarkedRight j) -
               f (effectiveNullaryMarkedLeft j)‖ ≤ L),
       ‖complexValuedPairCommutatorCLM
         (fun j => (2 : ℝ)^j)
         (fun j => (dist (effectiveNullaryMarkedLeft j)
           (effectiveNullaryMarkedRight j))⁻¹)
         (fun j => f (effectiveNullaryMarkedLeft j))
         (fun j => f (effectiveNullaryMarkedRight j))
         L hL hEdge‖ ≤ 1 →
       ‖f x - f y‖ ≤ dist x y) ∧
    ∃ (f : C(T.CompleteType Empty, ℂ)),
      f ∈ effectiveNullaryStoneSpectralTriple.observables ∧
      ∃ (hEdge : ∀ j,
        |(dist (effectiveNullaryMarkedLeft j)
            (effectiveNullaryMarkedRight j))⁻¹| *
          ‖f (effectiveNullaryMarkedRight j) -
            f (effectiveNullaryMarkedLeft j)‖ ≤ 1),
        ‖complexValuedPairCommutatorCLM
          (fun j => (2 : ℝ)^j)
          (fun j => (dist (effectiveNullaryMarkedLeft j)
            (effectiveNullaryMarkedRight j))⁻¹)
          (fun j => f (effectiveNullaryMarkedLeft j))
          (fun j => f (effectiveNullaryMarkedRight j))
          1 (by norm_num) hEdge‖ ≤ 1 ∧
        ‖f x - f y‖ = dist x y := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  rw [effectiveNullaryStoneSpectralTriple_eq_explicit]
  exact explicitDensePairSpectralTriple_metric_recovery
    effectiveNullaryDenseSeq effectiveNullaryDenseSeq_dense
    effectiveNullaryDenseMarkA effectiveNullaryDenseMarkB
    effectiveNullaryDenseMark_distinct x y

end Neoplatonic.LTR.Nullary
