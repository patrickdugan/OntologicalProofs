import Neoplatonic.LTR.SixDimensionalSignedOppositeRankOne
import Neoplatonic.LTR.SixDimensionalSignedOppositeRankOneMinus
import Neoplatonic.LTR.SixDimensionalSignedCornerComplementaryProjections
import Mathlib.Tactic

/-!
# LTR-MAN-100: original-coordinate opposite-block Gram decomposition

MAN-94/97 splits the saturated corner by X² + YYᴴ = C.
MAN-95/96 identifies the unique surviving opposite Dirac block
as rank one with singular value one half.

For the actual labelled six-dimensional Dirac witness, the corner X
has *only* the two off-diagonal truth-atom blocks, so X² equals
the sum of their two positive Gram matrices.

In the 00/11 positive branch, with B = D_{03},
T = (2i) B, one obtains

    X² = T Tᴴ + Tᴴ T.

The same holds for the 01/10 negative branch with T=(-2i)D_{12}.
This transports the MAN-96 Gram projections into MAN-97's exact
corner splitting without choosing an orthonormal singular-vector
basis or assuming any canonical chart.

The next stage identifies the rank-one complements of these two
Gram projections with the neutral-exchange image.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The square of an off-diagonal compression on two disjoint
truth atoms is the sum of its two oriented Gram terms. -/
theorem sixMatrix_disjointCorner_square
    (W P R : SixMat)
    (hPWP : P * W * P = 0)
    (hRWR : R * W * R = 0)
    (hPR : P * R = 0)
    (hRP : R * P = 0) :
    ((P + R) * W * (P + R)) *
      ((P + R) * W * (P + R)) =
      (P * W * R) * (R * W * P) +
        (R * W * P) * (P * W * R) := by
  let B : SixMat := P * W * R
  let Z : SixMat := R * W * P
  have hX : (P + R) * W * (P + R) = B + Z := by
    dsimp [B, Z]
    calc
      (P + R) * W * (P + R) =
          P * W * P + P * W * R + R * W * P + R * W * R := by
            noncomm_ring
      _ = P * W * R + R * W * P := by rw [hPWP,hRWR]; simp
  have hBB : B * B = 0 := by
    dsimp [B]
    calc
      (P * W * R) * (P * W * R) =
          P * W * (R * P) * W * R := by noncomm_ring
      _ = 0 := by rw [hRP]; simp
  have hZZ : Z * Z = 0 := by
    dsimp [Z]
    calc
      (R * W * P) * (R * W * P) =
          R * W * (P * R) * W * P := by noncomm_ring
      _ = 0 := by rw [hPR]; simp
  rw [hX]
  change (B + Z) * (B + Z) = B * Z + Z * B
  calc
    (B + Z) * (B + Z) = B * B + B * Z + Z * B + Z * Z := by
      noncomm_ring
    _ = B * Z + Z * B := by rw [hBB,hZZ]; simp

/-- With Hermitian witness and truth-atom projectors, the two
oriented corner blocks are conjugate-transposes. -/
theorem sixMatrix_disjointCorner_hermitianGram
    (W P R : SixMat)
    (hWH : W.IsHermitian)
    (hPH : P.IsHermitian)
    (hRH : R.IsHermitian)
    (hPWP : P * W * P = 0)
    (hRWR : R * W * R = 0)
    (hPR : P * R = 0)
    (hRP : R * P = 0) :
    ((P + R) * W * (P + R)) *
      ((P + R) * W * (P + R)) =
      (P * W * R) * (P * W * R).conjTranspose +
        (P * W * R).conjTranspose * (P * W * R) := by
  have hZ : (P * W * R).conjTranspose = R * W * P := by
    simp [Matrix.conjTranspose_mul, hWH.eq, hPH.eq, hRH.eq,
      Matrix.mul_assoc]
  rw [hZ]
  exact sixMatrix_disjointCorner_square W P R
    hPWP hRWR hPR hRP

/-- The actual saturated positive signed Hamming witness corner
has an exact square equal to the two Gram terms of its oriented
00-to-11 Dirac block, scaled by 2i. -/
theorem sixLabelled_exactHamming_saturated03_cornerSquare_oppositeGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let B := sixTruthFibreBlock label D 0 3
    let T := ((2 : ℂ) * Complex.I) • B
    let X := sixComplementCornerBlock W Q
    X * X = T * T.conjTranspose + T.conjTranspose * T := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let P : SixMat := sixTruthFibreProjection label 0
  let R : SixMat := sixTruthFibreProjection label 3
  let B : SixMat := sixTruthFibreBlock label D 0 3
  let T : SixMat := ((2 : ℂ) * Complex.I) • B
  let X : SixMat := sixComplementCornerBlock W Q
  change X * X = T * T.conjTranspose + T.conjTranspose * T
  have hC : (1 - Q : SixMat) = P + R :=
    sixPlus_complement_eq_oppositeFibreProjections label
  have hWH : W.IsHermitian :=
    sixLabelled_plusWitness_isHermitian label D hD
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_isHermitian
        label (fun u : Fin 4 => u = 0)
  have hRH : R.IsHermitian := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_isHermitian
        label (fun u : Fin 4 => u = 3)
  obtain ⟨hPR, hRP⟩ :=
    sixOpposite03_fibreProjections_orthogonal label
  obtain ⟨hPWP, hRWR⟩ :=
    sixLabelled_plusWitness_oppositeInternalBlocks_zero label D
  change P * W * P = 0 at hPWP
  change R * W * R = 0 at hRWR
  have hX : X * X =
      (P * W * R) * (P * W * R).conjTranspose +
        (P * W * R).conjTranspose * (P * W * R) := by
    dsimp [X, sixComplementCornerBlock]
    rw [hC]
    exact sixMatrix_disjointCorner_hermitianGram
      W P R hWH hPH hRH hPWP hRWR hPR hRP
  have hT : P * W * R = T := by
    change sixTruthFibreBlock label W 0 3 = T
    exact sixLabelled_sumWitness_opposite03_block label D
  rw [hT] at hX
  exact hX

/-- The actual negative signed witness has the corresponding
two Gram squares of the (-2i)-scaled 01-to-10 Dirac block. -/
theorem sixLabelled_exactHamming_saturated12_cornerSquare_oppositeGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    let W := labelledSquareA label D - labelledSquareB label D
    let Q := sixTruthSectorProjection label squareMinusNeutral
    let B := sixTruthFibreBlock label D 1 2
    let T := ((-2 : ℂ) * Complex.I) • B
    let X := sixComplementCornerBlock W Q
    X * X = T * T.conjTranspose + T.conjTranspose * T := by
  dsimp only
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  let P : SixMat := sixTruthFibreProjection label 1
  let R : SixMat := sixTruthFibreProjection label 2
  let B : SixMat := sixTruthFibreBlock label D 1 2
  let T : SixMat := ((-2 : ℂ) * Complex.I) • B
  let X : SixMat := sixComplementCornerBlock W Q
  change X * X = T * T.conjTranspose + T.conjTranspose * T
  have hC : (1 - Q : SixMat) = P + R :=
    sixMinus_complement_eq_oppositeFibreProjections label
  have hWH : W.IsHermitian :=
    sixLabelled_minusWitness_isHermitian label D hD
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_isHermitian
        label (fun u : Fin 4 => u = 1)
  have hRH : R.IsHermitian := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_isHermitian
        label (fun u : Fin 4 => u = 2)
  obtain ⟨hPR, hRP⟩ :=
    sixOpposite12_fibreProjections_orthogonal label
  obtain ⟨hPWP, hRWR⟩ :=
    sixLabelled_minusWitness_oppositeInternalBlocks_zero label D
  change P * W * P = 0 at hPWP
  change R * W * R = 0 at hRWR
  have hX : X * X =
      (P * W * R) * (P * W * R).conjTranspose +
        (P * W * R).conjTranspose * (P * W * R) := by
    dsimp [X, sixComplementCornerBlock]
    rw [hC]
    exact sixMatrix_disjointCorner_hermitianGram
      W P R hWH hPH hRH hPWP hRWR hPR hRP
  have hT : P * W * R = T := by
    change sixTruthFibreBlock label W 1 2 = T
    apply sixTruthFibreBlock_smul_of_entries
    intro i j hi hj
    simp [W, Matrix.sub_apply, labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, hj] <;> ring
  rw [hT] at hX
  exact hX

end Neoplatonic.LTR
