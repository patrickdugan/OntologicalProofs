import Neoplatonic.LTR.SixDimensionalSingletonInputOperatorNorm
import Neoplatonic.LTR.SixDimensionalNeutralUndirectedEdgeNorm
import Neoplatonic.LTR.SixDimensionalTransitionGramPositivity
import Neoplatonic.LTR.SixDimensionalSaturated03TransitionTrace
import Mathlib.Tactic

/-!
# LTR-MAN-130: singleton neutral edge squared norm equals transition trace

MAN-128 proves that the Hermitian undirected neutral edge
E=PYN+NYᴴP has squared operator norm equal to that of K=PYN
when P,N are orthogonal Hermitian projections.

MAN-122 proves that a singleton input N has squared Hilbert
operator norm equal to the squared Frobenius energy of K.
MAN-118 identifies that same energy with the complex trace
Tr(P Y N Yᴴ).

This module composes those certificates without a choice of
canonical U(2) basis. An individual transition trace bounded
above by 1/2 therefore bounds the actual undirected edge's
squared operator norm by 1/2.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A singleton truth input fibre turns a transition trace
into the exact squared norm of its undirected neutral edge. -/
theorem sixMatrix_singletonNeutralEdge_trace_eq_normSq
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hMult : truthMultiplicity label u = 1)
    (P Y : SixMat)
    (hPid : P * P = P) (hPH : P.IsHermitian)
    (hPN : P * sixTruthFibreProjection label u = 0)
    (hNP : sixTruthFibreProjection label u * P = 0) :
    ∃ e : ℝ, 0 ≤ e ∧
      sixMatrix_transitionTrace P Y (sixTruthFibreProjection label u) =
        (e : ℂ) ∧
      ‖sixMatrix_neutralUndirectedEdge
          P (sixTruthFibreProjection label u) Y‖ *
        ‖sixMatrix_neutralUndirectedEdge
          P (sixTruthFibreProjection label u) Y‖ = e := by
  let N : SixMat := sixTruthFibreProjection label u
  let K : SixMat := P * Y * N
  let e : ℝ := ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2
  have hNid : N * N = N := by
    simpa only [N, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label
        (fun v : Fin 4 => v = u))
  have hNH : N.IsHermitian := by
    simpa only [N, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_isHermitian label
        (fun v : Fin 4 => v = u))
  have hKN : K * N = K := by
    change (P * Y * N) * N = P * Y * N
    calc
      (P * Y * N) * N = P * Y * (N * N) := by noncomm_ring
      _ = P * Y * N := by rw [hNid]
  have he : 0 ≤ e := by
    dsimp [e]
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg _
  have hKsq : ‖K‖ * ‖K‖ = e := by
    simpa only [e] using
      (sixMatrix_singletonInput_opNormSq_eq_entryEnergy
        label u hMult K hKN)
  have hTrace : sixMatrix_transitionTrace P Y N = (e : ℂ) := by
    calc
      sixMatrix_transitionTrace P Y N =
          (K * K.conjTranspose).trace :=
        sixMatrix_transitionTrace_eq_gramTrace
          P N Y hPid hNid hPH hNH
      _ = (e : ℂ) := sixMatrix_gram_trace_eq_entryEnergy K
  have hE : ‖sixMatrix_neutralUndirectedEdge P N Y‖ *
        ‖sixMatrix_neutralUndirectedEdge P N Y‖ = e := by
    calc
      _ = ‖K‖ * ‖K‖ :=
        sixMatrix_neutralUndirectedEdge_normSq_eq_orientedNormSq
          P N Y hPH hNH hPN hNP
      _ = e := hKsq
  exact ⟨e, he, hTrace, hE⟩

/-- Bounding one original-coordinate transition trace by one
half bounds its Hermitian edge squared norm by one half. -/
theorem sixMatrix_singletonNeutralEdge_halfEnergy_normSq_le
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hMult : truthMultiplicity label u = 1)
    (P Y : SixMat)
    (hPid : P * P = P) (hPH : P.IsHermitian)
    (hPN : P * sixTruthFibreProjection label u = 0)
    (hNP : sixTruthFibreProjection label u * P = 0)
    (a : ℝ)
    (hTrace : sixMatrix_transitionTrace P Y
      (sixTruthFibreProjection label u) = (a : ℂ))
    (ha : a ≤ (1 / 2 : ℝ)) :
    ‖sixMatrix_neutralUndirectedEdge
        P (sixTruthFibreProjection label u) Y‖ *
      ‖sixMatrix_neutralUndirectedEdge
        P (sixTruthFibreProjection label u) Y‖ ≤
        (1 / 2 : ℝ) := by
  obtain ⟨e, he, hTe, hNorm⟩ :=
    sixMatrix_singletonNeutralEdge_trace_eq_normSq
      label u hMult P Y hPid hPH hPN hNP
  have heq : e = a := by
    apply Complex.ofReal_injective
    exact hTe.symm.trans hTrace
  calc
    ‖sixMatrix_neutralUndirectedEdge
        P (sixTruthFibreProjection label u) Y‖ *
      ‖sixMatrix_neutralUndirectedEdge
        P (sixTruthFibreProjection label u) Y‖ = e := hNorm
    _ = a := heq
    _ ≤ (1 / 2 : ℝ) := ha

end Neoplatonic.LTR
