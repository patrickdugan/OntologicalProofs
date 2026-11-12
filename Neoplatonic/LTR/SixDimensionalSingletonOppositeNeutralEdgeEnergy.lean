import Neoplatonic.LTR.SixDimensionalFourthEdgeHermitian
import Neoplatonic.LTR.SixDimensionalActualNeutralEdgeOrthogonality
import Neoplatonic.LTR.SixDimensionalSingletonInputOperatorNorm
import Neoplatonic.LTR.SixDimensionalNeutralUndirectedEdgeNorm
import Neoplatonic.LTR.SixDimensionalTruthBlockHermitianEnergy
import Mathlib.Tactic

/-!
# LTR-MAN-159: opposite-neutral fourth-edge energy controls its actual operator norm

MAN-154 adds the genuine 01/10 undirected fourth edge J to the
nonsaturated coordinate decomposition. MAN-155 then requires a bound
on its actual six-dimensional Hilbert operator norm.

The oriented 01->10 block of the first imaginary coordinate operator
A is exactly -i times the corresponding original Dirac block.
Its squared entry energy is therefore the original E12.

When the input truth fibre 10 is a singleton, MAN-122 identifies the
oriented block's squared operator norm with that entry energy. MAN-128
identifies the Hermitian undirected edge's squared norm with the
oriented norm. This proves ||J||^2 = E12 directly in the original
six-dimensional coordinates, without a unitary gauge.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The first-coordinate imaginary commutator has coefficient -i
on the oriented 01-to-10 truth-fibre block. -/
theorem sixLabelled_firstCoordinate_opposite12_orientedBlock
    (label : Fin 6 → Fin 4) (D : SixMat) :
    sixTruthFibreBlock label (labelledSquareA label D) 1 2 =
      (-Complex.I) • sixTruthFibreBlock label D 1 2 := by
  apply sixTruthFibreBlock_smul_of_entries
  intro i j hi hj
  simp [labelledSquareA, squareTruthBitP, hi, hj, smul_eq_mul]

/-- Multiplication by the unit complex scalar -i preserves the
oriented block's sum of squared entry magnitudes. -/
theorem sixLabelled_firstCoordinate_opposite12_energy_eq
    (label : Fin 6 → Fin 4) (D : SixMat) :
    sixTruthFibreBlockEnergy label (labelledSquareA label D) 1 2 =
      sixTruthFibreBlockEnergy label D 1 2 := by
  unfold sixTruthFibreBlockEnergy
  rw [sixLabelled_firstCoordinate_opposite12_orientedBlock label D]
  simp only [Matrix.smul_apply, norm_smul]
  norm_num

/-- For singleton 10 input, the genuine fourth undirected edge
has squared Euclidean operator norm equal to the oriented original
Dirac energy E12. This is an exact original-coordinate statement. -/
theorem sixLabelled_singletonNeutral2_fourthEdge_normSq_eq_energy12
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hMult : truthMultiplicity label 2 = 1) :
    ‖sixPlusOppositeNeutralEdge label D‖ *
      ‖sixPlusOppositeNeutralEdge label D‖ =
      sixTruthFibreBlockEnergy label D 1 2 := by
  let A : SixMat := labelledSquareA label D
  let P : SixMat := sixTruthFibreProjection label 1
  let N : SixMat := sixTruthFibreProjection label 2
  let K : SixMat := P * A * N
  have hA : A.IsHermitian :=
    sixLabelled_firstCoordinate_isHermitian label D hD
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 1))
  have hNH : N.IsHermitian := by
    simpa only [N, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 2))
  have hPN : P * N = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 2 (by decide)
  have hNP : N * P = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 1 (by decide)
  have hNid : N * N = N := by
    simpa only [N, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 2))
  have hKN : K * N = K := by
    dsimp [K]
    calc
      (P * A * N) * N = P * A * (N * N) := by noncomm_ring
      _ = P * A * N := by rw [hNid]
  have hJ : sixPlusOppositeNeutralEdge label D =
      sixMatrix_neutralUndirectedEdge P N A := by
    change P * A * N + N * A * P =
      P * A * N + N * A.conjTranspose * P
    rw [hA.eq]
  have hNorm : ‖sixPlusOppositeNeutralEdge label D‖ *
      ‖sixPlusOppositeNeutralEdge label D‖ =
        ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2 := by
    rw [hJ]
    calc
      ‖sixMatrix_neutralUndirectedEdge P N A‖ *
          ‖sixMatrix_neutralUndirectedEdge P N A‖ =
          ‖K‖ * ‖K‖ := by
            simpa only [K] using
              (sixMatrix_neutralUndirectedEdge_normSq_eq_orientedNormSq
                P N A hPH hNH hPN hNP)
      _ = ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2 :=
        sixMatrix_singletonInput_opNormSq_eq_entryEnergy
          label 2 hMult K hKN
  calc
    ‖sixPlusOppositeNeutralEdge label D‖ *
        ‖sixPlusOppositeNeutralEdge label D‖ =
          ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2 := hNorm
    _ = sixTruthFibreBlockEnergy label A 1 2 := rfl
    _ = sixTruthFibreBlockEnergy label D 1 2 :=
      sixLabelled_firstCoordinate_opposite12_energy_eq label D

/-- For singleton 01 input, reverse the Hermitian oriented block.
The exact original 01/10 Dirac entry energy is symmetric under
reversing the two truth fibres. -/
theorem sixLabelled_singletonNeutral1_fourthEdge_normSq_eq_energy12
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hMult : truthMultiplicity label 1 = 1) :
    ‖sixPlusOppositeNeutralEdge label D‖ *
      ‖sixPlusOppositeNeutralEdge label D‖ =
      sixTruthFibreBlockEnergy label D 1 2 := by
  let A : SixMat := labelledSquareA label D
  let P : SixMat := sixTruthFibreProjection label 2
  let N : SixMat := sixTruthFibreProjection label 1
  let K : SixMat := P * A * N
  have hA : A.IsHermitian :=
    sixLabelled_firstCoordinate_isHermitian label D hD
  have hAentries : ∀ i j, A i j = star (A j i) := by
    intro i j
    have h := congrArg (fun M : SixMat => M i j) hA.eq
    simpa only [Matrix.conjTranspose_apply] using h.symm
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 2))
  have hNH : N.IsHermitian := by
    simpa only [N, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 1))
  have hPN : P * N = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 1 (by decide)
  have hNP : N * P = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 2 (by decide)
  have hNid : N * N = N := by
    simpa only [N, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 1))
  have hKN : K * N = K := by
    dsimp [K]
    calc
      (P * A * N) * N = P * A * (N * N) := by noncomm_ring
      _ = P * A * N := by rw [hNid]
  have hJ : sixPlusOppositeNeutralEdge label D =
      sixMatrix_neutralUndirectedEdge P N A := by
    change N * A * P + P * A * N =
      P * A * N + N * A.conjTranspose * P
    rw [hA.eq]
    abel
  have hNorm : ‖sixPlusOppositeNeutralEdge label D‖ *
      ‖sixPlusOppositeNeutralEdge label D‖ =
        ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2 := by
    rw [hJ]
    calc
      ‖sixMatrix_neutralUndirectedEdge P N A‖ *
          ‖sixMatrix_neutralUndirectedEdge P N A‖ =
          ‖K‖ * ‖K‖ := by
            simpa only [K] using
              (sixMatrix_neutralUndirectedEdge_normSq_eq_orientedNormSq
                P N A hPH hNH hPN hNP)
      _ = ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2 :=
        sixMatrix_singletonInput_opNormSq_eq_entryEnergy
          label 1 hMult K hKN
  calc
    ‖sixPlusOppositeNeutralEdge label D‖ *
        ‖sixPlusOppositeNeutralEdge label D‖ =
          ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2 := hNorm
    _ = sixTruthFibreBlockEnergy label A 2 1 := rfl
    _ = sixTruthFibreBlockEnergy label A 1 2 :=
      (sixTruthFibreBlockEnergy_reverse label A hAentries 1 2).symm
    _ = sixTruthFibreBlockEnergy label D 1 2 :=
      sixLabelled_firstCoordinate_opposite12_energy_eq label D

/-- Either singleton neutral truth fibre suffices for the
exact J squared-norm to original E12 energy identity. -/
theorem sixLabelled_singletonNeutralEither_fourthEdge_normSq_eq_energy12
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hMult : truthMultiplicity label 1 = 1 ∨
      truthMultiplicity label 2 = 1) :
    ‖sixPlusOppositeNeutralEdge label D‖ *
      ‖sixPlusOppositeNeutralEdge label D‖ =
      sixTruthFibreBlockEnergy label D 1 2 := by
  rcases hMult with h1 | h2
  · exact sixLabelled_singletonNeutral1_fourthEdge_normSq_eq_energy12
      label D hD h1
  · exact sixLabelled_singletonNeutral2_fourthEdge_normSq_eq_energy12
      label D hD h2

end Neoplatonic.LTR
