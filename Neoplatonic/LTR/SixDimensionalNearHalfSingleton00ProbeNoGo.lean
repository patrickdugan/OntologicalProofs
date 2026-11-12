import Neoplatonic.LTR.SixDimensionalSingletonOutputProbeBridge
import Neoplatonic.LTR.SixDimensionalUniformHalfCornerBound
import Neoplatonic.LTR.SixDimensionalSaturated03Singleton00NoGo
import Neoplatonic.LTR.SixDimensionalActualNeutralEdgeIdentification
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-170: original near-half singleton-00 separating-probe obstruction

MAN-168 bounds the whole 00-to-neutral signed exchange row energy by
4ε when the 00 truth fibre is singleton. MAN-169 identifies this row
energy with the squared Hilbert operator norm of its undirected edge.

For ε=1/250, the row edge has norm strictly below 1/4. The exact
nonsaturated triple-separating probe identity reads

  K_(0,3,3,2) = J (A+B) J + 4 E_(00,neutral).

Its operator norm is at most 2. Scaling the probe by 1/2 gives a
Dirac-admissible observable with a 3/2 gap across the 00-01 edge,
contradicting the exact Connes Hamming distance one.

The proof uses the single original complex 6×6 Hermitian Dirac
matrix and never assumes pure Pauli spectral saturation.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- In the genuine positive Dirac witness, a singleton 00 output
fibre makes the squared norm of the complete undirected 00-neutral
edge equal the sum of its two original transition trace energies. -/
theorem sixLabelled_plusWitness_singleton00_neutralEdge_normSq_eq_rowEnergy
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hm0 : truthMultiplicity label 0 = 1) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let Y := (1 - Q : SixMat) * W * Q
    let P0 := sixTruthFibreProjection label 0
    let E0 := sixMatrix_neutralUndirectedEdge P0 Q Y
    ‖E0‖ * ‖E0‖ =
      (sixMatrix_transitionTrace P0 Y
        (sixTruthFibreProjection label 1)).re +
      (sixMatrix_transitionTrace P0 Y
        (sixTruthFibreProjection label 2)).re := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let Y : SixMat := (1 - Q) * W * Q
  let P0 : SixMat := sixTruthFibreProjection label 0
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  let E0 : SixMat := sixMatrix_neutralUndirectedEdge P0 Q Y
  change ‖E0‖ * ‖E0‖ =
    (sixMatrix_transitionTrace P0 Y N1).re +
      (sixMatrix_transitionTrace P0 Y N2).re
  have hQ2 : Q * Q = Q :=
    sixTruthSectorProjection_idempotent label squarePlusNeutral
  have hQH : Q.IsHermitian :=
    sixTruthSectorProjection_isHermitian label squarePlusNeutral
  have hP0H : P0.IsHermitian := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 0))
  have hP0Q : P0 * Q = 0 :=
    sixPlusNeutral_fibre00_orthogonal label
  have hQP0 : Q * P0 = 0 := by
    have h := congrArg Matrix.conjTranspose hP0Q
    simpa only [Matrix.conjTranspose_mul, hP0H.eq,
      hQH.eq, Matrix.conjTranspose_zero] using h
  have hSq := sixMatrix_singletonOutputEdge_normSq_eq_transitionTraceRe
    label 0 hm0 Q Y hQ2 hQH hQP0 hP0Q
  change ‖E0‖ * ‖E0‖ =
    (sixMatrix_transitionTrace P0 Y Q).re at hSq
  have hQsplit : Q = N1 + N2 :=
    sixPlusNeutral_eq_fibre01_add_fibre10 label
  have hTraceSum : sixMatrix_transitionTrace P0 Y Q =
      sixMatrix_transitionTrace P0 Y N1 +
        sixMatrix_transitionTrace P0 Y N2 := by
    rw [hQsplit]
    unfold sixMatrix_transitionTrace
    rw [← Matrix.trace_add]
    congr 1
    noncomm_ring
  rw [hTraceSum, Complex.add_re] at hSq
  exact hSq

/-- The actual singleton 00 chart cannot realize exact two-bit
Connes Hamming distances with positive Pauli overlap within 1/250
of its forbidden one-half endpoint. -/
theorem sixLabelled_exactHamming_positiveNearHalf_singleton00_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm0 : truthMultiplicity label 0 = 1)
    (hnear : (1 / 2 : ℝ) - (1 / 250 : ℝ) ≤
      sixOrientedOppositeEnergyImbalance label D) :
    False := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let Y : SixMat := (1 - Q) * W * Q
  let P0 : SixMat := sixTruthFibreProjection label 0
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  let E0 : SixMat := sixMatrix_neutralUndirectedEdge P0 Q Y
  let E01 : SixMat := sixMatrix_neutralUndirectedEdge P0 N1 Y
  let E02 : SixMat := sixMatrix_neutralUndirectedEdge P0 N2 Y
  let J : SixMat := sixTriple03SignMatrix label
  have hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D := by
    linarith
  have hRowBudget :=
    (sixLabelled_exactHamming_positiveNearHalf_singletonCorner_rowBudget
      label D hD hham (1 / 250 : ℝ) hc hnear).1 hm0
  change (sixMatrix_transitionTrace P0 Y N1).re +
    (sixMatrix_transitionTrace P0 Y N2).re ≤
      4 * (1 / 250 : ℝ) at hRowBudget
  have hEdgeSq :=
    sixLabelled_plusWitness_singleton00_neutralEdge_normSq_eq_rowEnergy
      label D hm0
  change ‖E0‖ * ‖E0‖ =
    (sixMatrix_transitionTrace P0 Y N1).re +
      (sixMatrix_transitionTrace P0 Y N2).re at hEdgeSq
  have hEdgeSqSmall : ‖E0‖ * ‖E0‖ ≤ (4 / 250 : ℝ) := by
    rw [hEdgeSq]
    linarith
  have hEdgeSmall : ‖E0‖ ≤ (1 / 4 : ℝ) := by
    nlinarith [norm_nonneg E0]
  have hQsplit : Q = N1 + N2 :=
    sixPlusNeutral_eq_fibre01_add_fibre10 label
  have hE0sum : E0 = E01 + E02 := by
    change sixMatrix_neutralUndirectedEdge P0 Q Y =
      sixMatrix_neutralUndirectedEdge P0 N1 Y +
        sixMatrix_neutralUndirectedEdge P0 N2 Y
    rw [hQsplit]
    unfold sixMatrix_neutralUndirectedEdge
    noncomm_ring
  have hE01truth : E01 = sixTruthUndirectedBlock label W 0 1 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 0 1 (Or.inl rfl) (Or.inl rfl)
  have hE02truth : E02 = sixTruthUndirectedBlock label W 0 2 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 0 2 (Or.inl rfl) (Or.inr rfl)
  have hE0truth : E0 =
      sixTruthUndirectedBlock label W 0 1 +
        sixTruthUndirectedBlock label W 0 2 := by
    rw [hE0sum, hE01truth, hE02truth]
  have hProbe := sixTriple03Probe_deviation_eq_fourNeutralEdges label D
  change sixTriple03ProbeImagComm label D =
    J * W * J +
      (4 : ℂ) • (sixTruthUndirectedBlock label W 0 1 +
        sixTruthUndirectedBlock label W 0 2) at hProbe
  rw [← hE0truth] at hProbe
  have hWbound : ‖W‖ ≤ (1 : ℝ) :=
    sixLabelled_exactHamming_plusWitness_norm_le_one
      label D hD hham
  have hJ2 : J * J = 1 :=
    sixTriple03SignMatrix_involution label
  have hJH : J.IsHermitian :=
    sixTriple03SignMatrix_hermitian label
  have hJbound : ‖J‖ ≤ (1 : ℝ) := by
    have hJNorm : ‖J‖ = (1 : ℝ) :=
      sixMatrix_hermitianInvolution_operatorNorm_one J hJH hJ2
    exact le_of_eq hJNorm
  have hProbeNorm :
      ‖sixTriple03ProbeImagComm label D‖ ≤ (2 : ℝ) := by
    rw [hProbe]
    exact sixMatrix_signPerturbedProbe_norm_le_two
      W J E0 hWbound hJbound hEdgeSmall
  have hProbeCLM :
      ‖(sixTriple03ProbeImagComm label D).toEuclideanLin.toContinuousLinearMap‖ ≤
        (2 : ℝ) := by
    change ‖sixTriple03ProbeImagComm label D‖ ≤ (2 : ℝ)
    exact hProbeNorm
  have hDiracNorm :
      ‖sixLabelledDiracComm label D squareTriple03Probe‖ ≤
        (2 : ℝ) := by
    rw [sixTriple03ProbeImagComm_eq_iDirac,
      sixLabelled_imaginaryOperator_norm] at hProbeCLM
    exact hProbeCLM
  let f : Fin 4 → ℂ := fun u => (1 / 2 : ℂ) * squareTriple03Probe u
  have hAdmissible : ‖sixLabelledDiracComm label D f‖ ≤ (1 : ℝ) := by
    change ‖sixLabelledDiracComm label D
      (fun u => (1 / 2 : ℂ) * squareTriple03Probe u)‖ ≤ (1 : ℝ)
    rw [sixLabelledDiracComm_smul, norm_smul]
    have hHalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hHalf]
    nlinarith
  have hd01 : sixLabelledConnesDistance label D 0 1 = 1 := by
    simpa [twoBitSquareHamming] using hham 0 1
  have hBound : ‖f 0 - f 1‖ ≤ (1 : ℝ) :=
    sixLabelledConnesDistance_bounds label D 0 1 1
      (by simpa [hd01]) f hAdmissible
  norm_num [f, squareTriple03Probe] at hBound

end Neoplatonic.LTR
