import Neoplatonic.LTR.SixDimensionalSignedWitnessPartialIsometry
import Neoplatonic.LTR.SixDimensionalNearHalfNeutralSingletons
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# LTR-MAN-174: overneutral signed-witness rank obstruction

A Hermitian 6×6 signed Hamming witness with a four-dimensional
zero neutral-neutral principal block can have matrix rank at most 4,
because the complementary block has dimension only 2.

This is an unsaturated finite-dimensional structural obstruction.
It depends on the actual truth-fibre block sparsity and contains
no Pauli-overlap or near-saturation hypothesis.

The proof proceeds through a general matrix rank subadditivity
lemma, the exact decomposition W=Q W (I-Q)+(I-Q) W when QWQ=0,
and an independent certificate of the rank of original diagonal
truth-sector projectors.

For m01=m10=1, the MINUS witness W=A-B has neutral truth
sector {00,11} of dimension 4, hence its rank is at most 4.

The next stage combines rank deficiency with the exact 4+2
residual Pauli square decomposition to force the minus residual
quadratic scalar to vanish throughout this multiplicity stratum.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Finite-dimensional rank of square complex matrices is
subadditive, transported through the concrete mulVec linear map. -/
theorem sixMatrix_rank_add_le
    (A B : SixMat) :
    (A + B).rank ≤ A.rank + B.rank := by
  classical
  change
    Module.finrank ℂ (LinearMap.range (A + B).mulVecLin) ≤
      Module.finrank ℂ (LinearMap.range A.mulVecLin) +
        Module.finrank ℂ (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_add]
  have hRange :
      LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
        LinearMap.range A.mulVecLin ⊔
          LinearMap.range B.mulVecLin := by
    intro x hx
    obtain ⟨v, rfl⟩ := hx
    apply Submodule.mem_sup.mpr
    refine ⟨A.mulVecLin v, ⟨v, rfl⟩,
      B.mulVecLin v, ⟨v, rfl⟩, ?_⟩
    simp
  exact (Submodule.finrank_mono hRange).trans
    (Submodule.finrank_add_le_finrank_add_finrank
      (LinearMap.range A.mulVecLin)
      (LinearMap.range B.mulVecLin))

/-- Any 6×6 matrix W whose compression to a neutral projector Q
vanishes has rank at most twice the complement rank. -/
theorem sixMatrix_zeroNeutral_rank_le_twoComplement
    (W Q : SixMat)
    (hQQ : Q * W * Q = 0) :
    W.rank ≤ 2 * (1 - Q : SixMat).rank := by
  let C : SixMat := 1 - Q
  have hDecomp : W = Q * W * C + C * W := by
    dsimp [C]
    calc
      W = Q * W * Q + Q * W * (1 - Q) +
        (1 - Q) * W := by noncomm_ring
      _ = Q * W * (1 - Q) + (1 - Q) * W := by
        rw [hQQ]
        simp
  rw [hDecomp]
  have h1 : (Q * W * C).rank ≤ C.rank :=
    Matrix.rank_mul_le_right (Q * W) C
  have h2 : (C * W).rank ≤ C.rank :=
    Matrix.rank_mul_le_left C W
  have h3 := sixMatrix_rank_add_le (Q * W * C) (C * W)
  change (Q * W * C + C * W).rank ≤ 2 * C.rank
  omega

/-- The rank of the original diagonal truth-fibre projector
is exactly the truth-atom multiplicity, in arbitrary coordinates. -/
theorem sixTruthFibreProjection_rank_eq_multiplicity
    (label : Fin 6 → Fin 4) (u : Fin 4) :
    (sixTruthFibreProjection label u).rank =
      truthMultiplicity label u := by
  classical
  change
    (Matrix.diagonal (fun i : Fin 6 =>
      if label i = u then (1 : ℂ) else 0)).rank =
        truthMultiplicity label u
  rw [Matrix.rank_diagonal]
  rw [Fintype.card_subtype]
  unfold truthMultiplicity
  congr 1
  ext i
  by_cases hi : label i = u <;> simp [hi]

/-- Complementing the minus-neutral {00,11} projector gives
precisely the plus-neutral {01,10} coordinate projector. -/
theorem sixMinusNeutral_complement_eq_plusNeutral
    (label : Fin 6 → Fin 4) :
    (1 - sixTruthSectorProjection label squareMinusNeutral : SixMat) =
      sixTruthSectorProjection label squarePlusNeutral := by
  ext i j
  by_cases hij : i = j
  · subst j
    generalize hli : label i = u
    fin_cases u <;>
      simp [sixTruthSectorProjection, squareMinusNeutral,
        squarePlusNeutral, Matrix.diagonal_apply, Matrix.one_apply, hli]
  · simp [sixTruthSectorProjection, Matrix.diagonal_apply,
      Matrix.one_apply, Matrix.sub_apply, hij]

/-- The 01/10 plus-neutral projector has rank equal to the
sum of its two constituent truth-fibre multiplicities. -/
theorem sixPlusNeutral_projection_rank_eq_fibreSum
    (label : Fin 6 → Fin 4) :
    (sixTruthSectorProjection label squarePlusNeutral).rank =
      truthMultiplicity label 1 + truthMultiplicity label 2 := by
  classical
  change
    (Matrix.diagonal (fun i : Fin 6 =>
      if squarePlusNeutral (label i) then (1 : ℂ) else 0)).rank =
        truthMultiplicity label 1 + truthMultiplicity label 2
  rw [Matrix.rank_diagonal, Fintype.card_subtype]
  calc
    (Finset.univ.filter (fun i : Fin 6 =>
      (if squarePlusNeutral (label i) then (1 : ℂ) else 0) ≠ 0)).card =
    (Finset.univ.filter (fun i : Fin 6 =>
      squarePlusNeutral (label i))).card := by
        congr 1
        ext i
        by_cases hi : squarePlusNeutral (label i) <;> simp [hi]
    _ = truthMultiplicity label 1 + truthMultiplicity label 2 :=
      sixPlusNeutral_card_eq_fibreSum label

/-- For singleton neutral truth fibres 01 and 10, the original
negative signed Dirac witness W=A-B has rank at most four,
regardless of either opposite energy and without saturation. -/
theorem sixLabelled_minusWitness_rank_le_four_of_neutralSingletons
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    (labelledSquareA label D -
      labelledSquareB label D).rank ≤ 4 := by
  let W : SixMat :=
    labelledSquareA label D - labelledSquareB label D
  let Q : SixMat :=
    sixTruthSectorProjection label squareMinusNeutral
  have hQQ : Q * W * Q = 0 :=
    sixTruthSectorProjection_W_zero label squareMinusNeutral _
      (sixLabelled_minusWitness_neutral_entry_zero label D)
  have hCRank : (1 - Q : SixMat).rank = 2 := by
    rw [sixMinusNeutral_complement_eq_plusNeutral]
    rw [sixPlusNeutral_projection_rank_eq_fibreSum label, hm1, hm2]
  have hRank := sixMatrix_zeroNeutral_rank_le_twoComplement W Q hQQ
  rw [hCRank] at hRank
  norm_num at hRank ⊢
  exact hRank

end Neoplatonic.LTR
