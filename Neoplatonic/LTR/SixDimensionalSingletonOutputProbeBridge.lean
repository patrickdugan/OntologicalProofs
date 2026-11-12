import Neoplatonic.LTR.SixDimensionalSingletonNeutralEdgeEnergy
import Neoplatonic.LTR.SixDimensionalTriple03ProbeHammingNoGo
import Neoplatonic.LTR.SixDimensionalNearHalfSingletonRowBudget
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-169: singleton-output edge norms and quantitative triple-probe identity

MAN-130 proves the edge norm/transition trace identity when the input
truth fibre is singleton. Swapping the directed channel and its
Hermitian adjoint gives the exact identity when its *output* truth
fibre is singleton.

The former saturated separating probe f=(0,3,3,2) satisfies, for
every actual original complex Dirac D,

  K_f = J W₊ J + 4(E_01 + E_02).

The extra term is supported on the 00-to-neutral truth edges. The
equation is exact regardless of spectral saturation, and no
vanishing-edge hypothesis is imposed.

When ||W₊||≤1 and ||E_01+E_02||≤1/4, the probe has norm at most 2.
The next integration uses MAN-168 to supply the small edge norm.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The square of the operator norm of a Hermitian undirected
truth-edge also equals its Gram transition real trace when the
OUTPUT truth fibre, rather than input, is singleton. -/
theorem sixMatrix_singletonOutputEdge_normSq_eq_transitionTraceRe
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hMult : truthMultiplicity label u = 1)
    (N Y : SixMat)
    (hNid : N * N = N) (hNH : N.IsHermitian)
    (hNP : N * sixTruthFibreProjection label u = 0)
    (hPN : sixTruthFibreProjection label u * N = 0) :
    ‖sixMatrix_neutralUndirectedEdge
        (sixTruthFibreProjection label u) N Y‖ *
      ‖sixMatrix_neutralUndirectedEdge
        (sixTruthFibreProjection label u) N Y‖ =
      (sixMatrix_transitionTrace
        (sixTruthFibreProjection label u) Y N).re := by
  let P : SixMat := sixTruthFibreProjection label u
  have hFlip : sixMatrix_neutralUndirectedEdge P N Y =
      sixMatrix_neutralUndirectedEdge N P Y.conjTranspose := by
    unfold sixMatrix_neutralUndirectedEdge
    simp only [Matrix.conjTranspose_conjTranspose]
    abel
  obtain ⟨e, he, hTrace, hNorm⟩ :=
    sixMatrix_singletonNeutralEdge_trace_eq_normSq
      label u hMult N Y.conjTranspose hNid hNH hNP hPN
  have hTraceFlip : sixMatrix_transitionTrace P Y N =
      sixMatrix_transitionTrace N Y.conjTranspose P := by
    unfold sixMatrix_transitionTrace
    calc
      (P * Y * N * Y.conjTranspose).trace =
          ((P * Y) * (N * Y.conjTranspose)).trace := by
            congr 1
            noncomm_ring
      _ = ((N * Y.conjTranspose) * (P * Y)).trace :=
        Matrix.trace_mul_comm (P * Y) (N * Y.conjTranspose)
      _ = (N * Y.conjTranspose * P * Y).trace := by
        congr 1
        noncomm_ring
  change sixMatrix_transitionTrace N Y.conjTranspose P = (e : ℂ)
    at hTrace
  change
    ‖sixMatrix_neutralUndirectedEdge P N Y‖ *
      ‖sixMatrix_neutralUndirectedEdge P N Y‖ =
        (sixMatrix_transitionTrace P Y N).re
  calc
    ‖sixMatrix_neutralUndirectedEdge P N Y‖ *
        ‖sixMatrix_neutralUndirectedEdge P N Y‖ =
      ‖sixMatrix_neutralUndirectedEdge N P Y.conjTranspose‖ *
        ‖sixMatrix_neutralUndirectedEdge N P Y.conjTranspose‖ := by
          rw [hFlip]
    _ = e := hNorm
    _ = (sixMatrix_transitionTrace P Y N).re := by
      rw [hTraceFlip, hTrace]
      simp

/-- The triple separating probe differs from the sign-conjugated
true plus witness by exactly four times the two 00-neutral edges.
This is a finite truth-table identity with no zero-row premise. -/
theorem sixTriple03Probe_deviation_eq_fourNeutralEdges
    (label : Fin 6 → Fin 4) (D : SixMat) :
    let W := labelledSquareA label D + labelledSquareB label D
    sixTriple03ProbeImagComm label D =
      sixTriple03SignMatrix label * W *
        sixTriple03SignMatrix label +
      (4 : ℂ) • (sixTruthUndirectedBlock label W 0 1 +
        sixTruthUndirectedBlock label W 0 2) := by
  dsimp only
  ext i j
  generalize hli : label i = u
  generalize hlj : label j = v
  fin_cases u <;> fin_cases v <;>
    simp [hli, hlj, sixTriple03ProbeImagComm,
      sixTriple03SignMatrix, sixTruthUndirectedBlock,
      sixTruthFibreBlock_entry,
      labelledSquareA, labelledSquareB,
      Matrix.add_apply, Matrix.smul_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal,
      squareTriple03Probe, squareTriple03Sign,
      squareTruthBitP, squareTruthBitQ] <;> ring

/-- The norm of an exact diagonal sign-conjugated plus witness
with a quarter-sized undirected error channel is at most two. -/
theorem sixMatrix_signPerturbedProbe_norm_le_two
    (W J E : SixMat)
    (hW : ‖W‖ ≤ (1 : ℝ))
    (hJ : ‖J‖ ≤ (1 : ℝ))
    (hE : ‖E‖ ≤ (1 / 4 : ℝ)) :
    ‖J * W * J + (4 : ℂ) • E‖ ≤ (2 : ℝ) := by
  have hJW : ‖J * W‖ ≤ (1 : ℝ) := by
    calc
      ‖J * W‖ ≤ ‖J‖ * ‖W‖ := Matrix.l2_opNorm_mul J W
      _ ≤ 1 := by nlinarith [norm_nonneg J, norm_nonneg W]
  have hJWJ : ‖J * W * J‖ ≤ (1 : ℝ) := by
    calc
      ‖J * W * J‖ ≤ ‖J * W‖ * ‖J‖ :=
        Matrix.l2_opNorm_mul (J * W) J
      _ ≤ 1 := by nlinarith [norm_nonneg (J * W), norm_nonneg J]
  have hFour : ‖(4 : ℂ) • E‖ ≤ (1 : ℝ) := by
    rw [norm_smul]
    norm_num at *
    linarith
  calc
    ‖J * W * J + (4 : ℂ) • E‖ ≤
      ‖J * W * J‖ + ‖(4 : ℂ) • E‖ := norm_add_le _ _
    _ ≤ 2 := by linarith

end Neoplatonic.LTR
