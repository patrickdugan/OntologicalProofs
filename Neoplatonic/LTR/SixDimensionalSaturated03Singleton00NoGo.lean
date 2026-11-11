import Neoplatonic.LTR.SixDimensionalSingletonNeutralRowExtinction
import Neoplatonic.LTR.SixDimensionalTriple03ProbeHammingNoGo
import Mathlib.Tactic

/-!
# LTR-MAN-109: exclude a singleton 00 fibre at positive saturation

MAN-106 proves P0 (C W+ Q)=0 for the actual saturated six-dimensional
Dirac witness W+=A+B when truth atom 00 has multiplicity one.

Since the 00 truth fibre projection P0 is orthogonal to the neutral
projection Q, the equation implies P0 W+ Q=0. The signed Hamming
coefficient on each 00-to-01/10 edge is exactly i, so the original
Dirac block D_{00,neutral} vanishes. Hermiticity gives the reverse
blocks too.

MAN-108 proves that this support extinction makes the probe
f=(0,3,3,2) unit-admissible, violating the exact edge
distance d(00,01)=1. Combining the two completes an actual
six-dimensional no-go theorem for the positive saturated
m_00=1 case, including the (1,1,1,3) fibre pattern.

The opposite singleton orientation and 2+2 case require further
specific proofs. This theorem assumes the pure saturation
e03=1/4,e12=0 explicitly.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Any matrix block P W Q vanishes if P is orthogonal to Q
and the corresponding neutral-exchange compression does. -/
theorem sixMatrix_neutralRow_zero_implies_fullRow_zero
    (P Q W : SixMat)
    (hPQ : P * Q = 0)
    (hPY : P * ((1 - Q) * W * Q) = 0) :
    P * W * Q = 0 := by
  have hPC : P * (1 - Q) = P := by
    calc
      P * (1 - Q) = P - P * Q := by noncomm_ring
      _ = P := by rw [hPQ]; simp
  calc
    P * W * Q = (P * (1 - Q)) * W * Q := by rw [hPC]
    _ = P * ((1 - Q) * W * Q) := by noncomm_ring
    _ = 0 := hPY

/-- The singleton 00 truth-atom projector is orthogonal to
the 01/10 neutral-sector projection in every labelled chart. -/
theorem sixPlusNeutral_fibre00_orthogonal
    (label : Fin 6 → Fin 4) :
    sixTruthFibreProjection label 0 *
      sixTruthSectorProjection label squarePlusNeutral = 0 := by
  ext i j
  simp only [sixTruthFibreProjection, sixTruthSectorProjection,
    Matrix.diagonal_mul]
  by_cases hi : label i = 0
  · simp [hi, squarePlusNeutral, Matrix.diagonal_apply]
  · simp [hi]

/-- Every 00-to-neutral matrix entry of the positive signed
witness is exactly i times the corresponding original Dirac entry. -/
theorem sixPlusWitness_00neutral_entry
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6)
    (hi : label i = 0)
    (hj : squarePlusNeutral (label j)) :
    (labelledSquareA label D + labelledSquareB label D) i j =
      Complex.I * D i j := by
  rcases hj with h1 | h2
  · simp [Matrix.add_apply, labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, h1] <;> ring
  · simp [Matrix.add_apply, labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, h2] <;> ring

/-- The original saturated Hermitian Dirac matrix has zero
couplings from a singleton 00 truth atom into the 01/10 neutral
truth sector, and conversely. This discharges the exact support
premise of MAN-108 from MAN-106. -/
theorem sixLabelled_exactHamming_saturated03_singleton00_noNeutralDirac
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 0 = 1) :
    ∀ i j : Fin 6, squareTriple03Bad (label i) (label j) →
      D i j = 0 := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let P : SixMat := sixTruthFibreProjection label 0
  have hPY : P * ((1 - Q) * W * Q) = 0 := by
    have h := sixLabelled_exactHamming_saturated03_singleton00_neutralRow_zero
      label D hD hham h03 h12 hMult
    change P * ((1 - Q) * W * Q) = 0 at h
    exact h
  have hPQ : P * Q = 0 :=
    sixPlusNeutral_fibre00_orthogonal label
  have hPWQ : P * W * Q = 0 :=
    sixMatrix_neutralRow_zero_implies_fullRow_zero P Q W hPQ hPY
  have hforward :
      ∀ i j : Fin 6, label i = 0 →
        squarePlusNeutral (label j) → D i j = 0 := by
    intro i j hi hj
    have hmatrix : (P * W * Q) i j = 0 := by rw [hPWQ]; rfl
    have hWzero : W i j = 0 := by
      simpa [P, Q, sixTruthFibreProjection,
        sixTruthSectorProjection, Matrix.diagonal_mul,
        Matrix.mul_diagonal, hi, hj] using hmatrix
    have hcoef : W i j = Complex.I * D i j :=
      sixPlusWitness_00neutral_entry label D i j hi hj
    rw [hcoef] at hWzero
    exact (mul_eq_zero.mp hWzero).resolve_left (by norm_num)
  intro i j hbad
  change (label i = 0 ∧
      (label j = 1 ∨ label j = 2)) ∨
    (label j = 0 ∧
      (label i = 1 ∨ label i = 2)) at hbad
  rcases hbad with ⟨hi, hj⟩ | ⟨hj, hi⟩
  · exact hforward i j hi hj
  · have hreverse : D j i = 0 := hforward j i hj hi
    rw [hD i j, hreverse]
    simp

/-- One of MAN-92's six saturated candidate fibre patterns
is impossible: if 00 has multiplicity one, a genuinely
Hermitian six-dimensional exact-Hamming representation cannot
have pure positive opposite-corner energy saturation. -/
theorem sixLabelled_exactHamming_saturated03_singleton00_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 0 = 1) :
    False := by
  exact sixLabelled_exactHamming_saturated03_zeroNeutralRows_impossible
    label D hD hham h03 h12
    (sixLabelled_exactHamming_saturated03_singleton00_noNeutralDirac
      label D hD hham h03 h12 hMult)

end Neoplatonic.LTR
