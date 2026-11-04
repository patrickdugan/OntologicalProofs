import Neoplatonic.LTR.LogicalHilbertUndecidability
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Exact Hilbert refutation norm gap and half-error obstruction

A represented sentence truth observable is a self-adjoint
idempotent in the complex C*-algebra B(H). The C*-identity
implies that its norm is either zero or exactly one.

For the refutation operator, zero means semantic entailment,
and one means its failure. Consequently any real-valued
numerical estimates with uniform absolute error strictly
less than 1/2 permit a threshold decision for entailment.

The final theorem makes the computability of the threshold
predicate an explicit assumption. In particular it excludes
any effective approximation procedure whose comparisons with
1/2 are computable, under the displayed undecidability premise.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language

universe u v w

variable {L : FirstOrder.Language.{u,v}} {T : L.Theory} {α : Type w}
variable [Countable (L.withConstants α).Sentence]

/-- Every named Hilbert truth projection has norm exactly zero
or one, by its self-adjoint idempotence and the C*-identity. -/
theorem logicalHilbertProjection_norm_zero_or_one
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence) :
    ‖logicalSentenceHilbertOp hT η hη φ‖ = 0 ∨
      ‖logicalSentenceHilbertOp hT η hη φ‖ = 1 := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  let P : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
    logicalSentenceHilbertOp hT η hη φ
  have hproj : P * P = P ∧ star P = P := by
    simpa only [P, logicalSentenceHilbertOp] using
      (logicalSentence_HilbertProjection hT η hη φ)
  have hnorm : ‖P‖ * ‖P‖ = ‖P‖ := by
    calc
      ‖P‖ * ‖P‖ = ‖star P * P‖ :=
        (CStarRing.norm_star_mul_self).symm
      _ = ‖P‖ := by rw [hproj.2, hproj.1]
  have hfactor : ‖P‖ * (‖P‖ - 1) = 0 := by
    nlinarith [hnorm]
  have hgap : ‖P‖ = 0 ∨ ‖P‖ = 1 := by
    rcases mul_eq_zero.mp hfactor with hz | ho
    · exact Or.inl hz
    · exact Or.inr (sub_eq_zero.mp ho)
  exact hgap

/-- Norm one of a represented refutation projector means exactly
the failure of entailment. -/
theorem logicalHilbertRefutationNorm_one_iff_not_entails
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence) :
    ‖logicalSentenceHilbertOp hT η hη φ.not‖ = 1 ↔
      ¬ ((L.lhomWithConstants α).onTheory T ⊨ᵇ φ) := by
  constructor
  · intro hOne hEnt
    have hZero :=
      (logicalHilbertRefutationNorm_zero_iff_entails hT η hη φ).mpr hEnt
    rw [hZero] at hOne
    norm_num at hOne
  · intro hNot
    rcases logicalHilbertProjection_norm_zero_or_one hT η hη φ.not
      with hZero | hOne
    · exact False.elim
        (hNot ((logicalHilbertRefutationNorm_zero_iff_entails
          hT η hη φ).mp hZero))
    · exact hOne

/-- An estimate of a Hilbert refutation norm with error below
one half crosses the threshold precisely for entailed sentences. -/
theorem logicalHilbertRefutationApprox_half_iff_entails
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence)
    (estimate : ℝ)
    (hAccuracy :
      |estimate - ‖logicalSentenceHilbertOp hT η hη φ.not‖| <
        (1 / 2 : ℝ)) :
    estimate < (1 / 2 : ℝ) ↔
      (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  constructor
  · intro hSmall
    by_contra hNot
    have hOne :=
      (logicalHilbertRefutationNorm_one_iff_not_entails
        hT η hη φ).mpr hNot
    rw [hOne] at hAccuracy
    have hBound := (abs_lt.mp hAccuracy).1
    linarith
  · intro hEnt
    have hZero :=
      (logicalHilbertRefutationNorm_zero_iff_entails
        hT η hη φ).mpr hEnt
    rw [hZero] at hAccuracy
    have hBound := (abs_lt.mp hAccuracy).2
    linarith

/-- An undecidable entailment predicate forbids a uniformly
half-accurate norm estimator with a computable half-threshold test.
The requested computable predicate is part of the explicit premise. -/
theorem logicalHilbertRefutation_no_computable_half_estimator
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (code : ℕ → (L.withConstants α).Sentence)
    (hUndecidable : ¬ ComputablePred
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n)) :
    ¬ ∃ (estimate : ℕ → ℝ),
      ComputablePred (fun n => estimate n < (1 / 2 : ℝ)) ∧
      ∀ n, |estimate n -
        ‖logicalSentenceHilbertOp hT η hη (code n).not‖| <
          (1 / 2 : ℝ) := by
  rintro ⟨estimate, hThreshold, hAccuracy⟩
  apply hUndecidable
  apply ComputablePred.of_eq hThreshold
  intro n
  exact logicalHilbertRefutationApprox_half_iff_entails
    hT η hη (code n) (estimate n) (hAccuracy n)

end Neoplatonic.LTR
