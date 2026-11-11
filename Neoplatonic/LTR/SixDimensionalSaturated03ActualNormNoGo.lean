import Neoplatonic.LTR.SixDimensionalBistochasticThreeEdgeNoGo
import Neoplatonic.LTR.SixDimensionalSaturatedHalfCornerNorm
import Neoplatonic.LTR.SixDimensionalSignedCornerTrueEdge
import Neoplatonic.LTR.SixDimensionalActualNeutralEdgeIdentification
import Neoplatonic.LTR.SixDimensionalSingletonNeutralEdgeEnergy
import Neoplatonic.LTR.SixDimensionalActualTransitionHalfEnergy
import Neoplatonic.LTR.SixDimensionalActualNeutralEdgeOrthogonality
import Neoplatonic.LTR.SixDimensionalSignedCoordinateThreeEdges
import Neoplatonic.LTR.SixDimensionalLabelledWitnesses
import Mathlib.Tactic

/-!
# LTR-MAN-135: the genuine six-dimensional positive-saturation Hamming no-go

At pure 00/11 saturation, the actual corner W=A+B is a Hermitian
involution. MAN-112 leaves the single possible fibre pattern
(2,1,1,2). The neutral exchange Y from MAN-94 has four adjacent
edges, with a positive bistochastic transition-energy table
whose first row has entries a,b and a+b=1.

MAN-125 proves all six product-zero conditions for the adjacent
edges. MAN-129 identifies those edges with original signed Dirac
truth-blocks. MAN-130 identifies their squared operator norms with
the transition traces. MAN-131/132 bound the shared opposite corner
by one half and identify it with the coordinate active channel.
MAN-126's three-edge identities give the true A and B matrices.
MAN-133's C*-norm obstruction then contradicts their Hamming-forced
unit lower bounds.

This theorem excludes pure positive saturation in the actual
six-dimensional faithful labelled spectral representation.
It is conditional on the saturation equations. Excluding all
non-saturated exact-Hamming configurations is a separate problem.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Undirected edge order does not depend on the orientation. -/
theorem sixTruthUndirectedBlock_swap
    (label : Fin 6 → Fin 4) (W : SixMat) (u v : Fin 4) :
    sixTruthUndirectedBlock label W u v =
      sixTruthUndirectedBlock label W v u := by
  unfold sixTruthUndirectedBlock
  abel

/-- A singleton neutral input makes the edge norm squared equal
to its real trace energy, with the scalar already identified. -/
theorem sixMatrix_singletonNeutralEdge_normSq_of_trace
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hMult : truthMultiplicity label u = 1)
    (P Y : SixMat)
    (hPid : P * P = P) (hPH : P.IsHermitian)
    (hPN : P * sixTruthFibreProjection label u = 0)
    (hNP : sixTruthFibreProjection label u * P = 0)
    (a : ℝ)
    (hTrace : sixMatrix_transitionTrace P Y
      (sixTruthFibreProjection label u) = (a : ℂ)) :
    ‖sixMatrix_neutralUndirectedEdge
      P (sixTruthFibreProjection label u) Y‖ *
      ‖sixMatrix_neutralUndirectedEdge
      P (sixTruthFibreProjection label u) Y‖ = a := by
  obtain ⟨e, _, hte, hnorm⟩ :=
    sixMatrix_singletonNeutralEdge_trace_eq_normSq
      label u hMult P Y hPid hPH hPN hNP
  have heq : e = a := by
    apply Complex.ofReal_injective
    exact hte.symm.trans hTrace
  exact hnorm.trans heq

/-- A pure 00/11-saturated exact two-bit Hamming Connes metric
cannot be represented by a Hermitian Dirac matrix on six complex
Hilbert coordinates, for any faithful labelled diagonal action. -/
theorem sixLabelled_exactHamming_saturated03_actualNorm_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    False := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  let H : SixMat := sixPlusActiveHalf label D
  let E01 : SixMat := sixMatrix_neutralUndirectedEdge P0 N1 Y
  let E32 : SixMat := sixMatrix_neutralUndirectedEdge P3 N2 Y
  let E02 : SixMat := sixMatrix_neutralUndirectedEdge P0 N2 Y
  let E31 : SixMat := sixMatrix_neutralUndirectedEdge P3 N1 Y
  obtain ⟨hm0, hm1, hm2, hm3⟩ :=
    sixLabelled_exactHamming_saturated03_onlyOppositeDoubles
      label D hsurj hD hham h03 h12
  have hP0id : P0 * P0 = P0 := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 0))
  have hP3id : P3 * P3 = P3 := by
    simpa only [P3, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 3))
  have hP0H : P0.IsHermitian := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 0))
  have hP3H : P3.IsHermitian := by
    simpa only [P3, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 3))
  have hN1H : N1.IsHermitian := by
    simpa only [N1, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 1))
  have hN2H : N2.IsHermitian := by
    simpa only [N2, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 2))
  have hP0N1 : P0 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 1 (by decide)
  have hN1P0 : N1 * P0 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 0 (by decide)
  have hP0N2 : P0 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 2 (by decide)
  have hN2P0 : N2 * P0 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 0 (by decide)
  have hP3N1 : P3 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 3 1 (by decide)
  have hN1P3 : N1 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 3 (by decide)
  have hP3N2 : P3 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 3 2 (by decide)
  have hN2P3 : N2 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 3 (by decide)
  have hWH : W.IsHermitian :=
    sixLabelled_plusWitness_isHermitian label D hD
  have hHH : H.IsHermitian := by
    have hh : (sixTruthUndirectedBlock label W 0 3).IsHermitian :=
      sixTruthUndirectedBlock_hermitian label W hWH 0 3
    change ((1 / 2 : ℂ) • sixTruthUndirectedBlock label W 0 3).conjTranspose =
      (1 / 2 : ℂ) • sixTruthUndirectedBlock label W 0 3
    rw [Matrix.conjTranspose_smul, hh.eq]
    norm_num
  have hE01H : E01.IsHermitian :=
    sixMatrix_neutralUndirectedEdge_hermitian P0 N1 Y hP0H hN1H
  have hE32H : E32.IsHermitian :=
    sixMatrix_neutralUndirectedEdge_hermitian P3 N2 Y hP3H hN2H
  have hE02H : E02.IsHermitian :=
    sixMatrix_neutralUndirectedEdge_hermitian P0 N2 Y hP0H hN2H
  have hE31H : E31.IsHermitian :=
    sixMatrix_neutralUndirectedEdge_hermitian P3 N1 Y hP3H hN1H
  have hHalf : H = (1 / 2 : ℂ) • X :=
    sixLabelled_plusActiveHalf_eq_trueCornerHalf label D
  have hHbound : ‖H‖ ≤ (1 / 2 : ℝ) := by
    rw [hHalf]
    exact sixLabelled_exactHamming_saturated03_halfCorner_norm_le
      label D hD hham h03 h12
  have hProducts :=
    sixLabelled_exactHamming_saturated03_actual_neutralEdges_products_zero
      label D hD hham h03 h12
  change X * E02 = 0 ∧ X * E31 = 0 ∧ E02 * E31 = 0 ∧
    X * E01 = 0 ∧ X * E32 = 0 ∧ E01 * E32 = 0 at hProducts
  obtain ⟨hXE02, hXE31, hE02E31, hXE01, hXE32, hE01E32⟩ :=
    hProducts
  have hHE01 : H * E01 = 0 := by
    rw [hHalf, Matrix.smul_mul, hXE01]
    simp
  have hHE32 : H * E32 = 0 := by
    rw [hHalf, Matrix.smul_mul, hXE32]
    simp
  have hHE02 : H * E02 = 0 := by
    rw [hHalf, Matrix.smul_mul, hXE02]
    simp
  have hHE31 : H * E31 = 0 := by
    rw [hHalf, Matrix.smul_mul, hXE31]
    simp
  have hE01block : E01 = sixTruthUndirectedBlock label W 0 1 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 0 1 (Or.inl rfl) (Or.inl rfl)
  have hE32block : E32 = sixTruthUndirectedBlock label W 3 2 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 3 2 (Or.inr rfl) (Or.inr rfl)
  have hE02block : E02 = sixTruthUndirectedBlock label W 0 2 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 0 2 (Or.inl rfl) (Or.inr rfl)
  have hE31block : E31 = sixTruthUndirectedBlock label W 3 1 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 3 1 (Or.inr rfl) (Or.inl rfl)
  have hA : labelledSquareA label D = H + E01 + E32 := by
    calc
      labelledSquareA label D = sixPlusCoordinateAEdges label D :=
        sixLabelled_exactHamming_zero12_coordinateA_threeEdges label D hD h12
      _ = H + E01 + E32 := by
        change H + sixTruthUndirectedBlock label W 0 1 +
          sixTruthUndirectedBlock label W 2 3 = H + E01 + E32
        rw [← hE01block, sixTruthUndirectedBlock_swap label W 2 3,
          ← hE32block]
  have hB : labelledSquareB label D = H + E02 + E31 := by
    calc
      labelledSquareB label D = sixPlusCoordinateBEdges label D :=
        sixLabelled_exactHamming_zero12_coordinateB_threeEdges label D hD h12
      _ = H + E02 + E31 := by
        change H + sixTruthUndirectedBlock label W 0 2 +
          sixTruthUndirectedBlock label W 1 3 = H + E02 + E31
        rw [← hE02block, sixTruthUndirectedBlock_swap label W 1 3,
          ← hE31block]
  obtain ⟨a, b, ha, hb, htrace01, htrace02, hab, _⟩ :=
    sixLabelled_exactHamming_saturated03_transitionHalfEnergy
      label D hsurj hD hham h03 h12
  change sixMatrix_transitionTrace P0 Y N1 = (a : ℂ) at htrace01
  change sixMatrix_transitionTrace P0 Y N2 = (b : ℂ) at htrace02
  have hPairs :=
    (sixLabelled_exactHamming_saturated03_oppositeDouble_transitionTrace
      label D hsurj hD hham h03 h12).2.2
  change sixMatrix_transitionTrace P0 Y N1 =
    sixMatrix_transitionTrace P3 Y N2 ∧
    sixMatrix_transitionTrace P0 Y N2 =
      sixMatrix_transitionTrace P3 Y N1 at hPairs
  obtain ⟨hpair01, hpair02⟩ := hPairs
  have htrace32 : sixMatrix_transitionTrace P3 Y N2 = (a : ℂ) :=
    hpair01.symm.trans htrace01
  have htrace31 : sixMatrix_transitionTrace P3 Y N1 = (b : ℂ) :=
    hpair02.symm.trans htrace02
  have hE01sq : ‖E01‖ * ‖E01‖ = a :=
    sixMatrix_singletonNeutralEdge_normSq_of_trace
      label 1 hm1 P0 Y hP0id hP0H hP0N1 hN1P0 a htrace01
  have hE32sq : ‖E32‖ * ‖E32‖ = a :=
    sixMatrix_singletonNeutralEdge_normSq_of_trace
      label 2 hm2 P3 Y hP3id hP3H hP3N2 hN2P3 a htrace32
  have hE02sq : ‖E02‖ * ‖E02‖ = b :=
    sixMatrix_singletonNeutralEdge_normSq_of_trace
      label 2 hm2 P0 Y hP0id hP0H hP0N2 hN2P0 b htrace02
  have hE31sq : ‖E31‖ * ‖E31‖ = b :=
    sixMatrix_singletonNeutralEdge_normSq_of_trace
      label 1 hm1 P3 Y hP3id hP3H hP3N1 hN1P3 b htrace31
  have hd01 : sixLabelledConnesDistance label D 0 1 = 1 := by
    simpa [twoBitSquareHamming] using hham 0 1
  have hd02 : sixLabelledConnesDistance label D 0 2 = 1 := by
    simpa [twoBitSquareHamming] using hham 0 2
  have hAunit : (1 : ℝ) ≤ ‖labelledSquareA label D‖ := by
    have hedges : ∀ f : Fin 4 → ℂ,
        ‖sixLabelledDiracComm label D f‖ ≤ 1 →
          ‖f 0 - f 1‖ ≤ 1 := by
      intro f hf
      exact sixLabelledConnesDistance_bounds label D 0 1 1
        (by simp [hd01]) f hf
    have h := sixLabelled_firstCoordinate_norm_ge_one label D hedges
    change (1 : ℝ) ≤ ‖labelledSquareA label D‖ at h
    exact h
  have hBunit : (1 : ℝ) ≤ ‖labelledSquareB label D‖ := by
    have hedges : ∀ f : Fin 4 → ℂ,
        ‖sixLabelledDiracComm label D f‖ ≤ 1 →
          ‖f 0 - f 2‖ ≤ 1 := by
      intro f hf
      exact sixLabelledConnesDistance_bounds label D 0 2 1
        (by simp [hd02]) f hf
    have h := sixLabelled_secondCoordinate_norm_ge_one label D hedges
    change (1 : ℝ) ≤ ‖labelledSquareB label D‖ at h
    exact h
  exact sixMatrix_bistochastic_threeEdge_unitNorm_impossible
    H E01 E32 E02 E31 (labelledSquareA label D) (labelledSquareB label D)
    hHH hE01H hE32H hE02H hE31H
    hHE01 hHE32 hE01E32 hHE02 hHE31 hE02E31
    hHbound a b ha hb hab
    hE01sq hE32sq hE02sq hE31sq hA hB hAunit hBunit

end Neoplatonic.LTR
