import Neoplatonic.LTR.SixDimensionalExactHammingAmbientInvolution
import Mathlib.Tactic

/-!
# LTR-MAN-93: the corner block of an involution with zero neutral block is tripotent

For a complex six-dimensional matrix involution W and a diagonal
projection Q onto a neutral truth sector, assume QWQ=0. Writing
P=I-Q and X=PWP, the full block matrix is

              W = [[X,Y],[Z,0]].

Squaring gives X²+YZ=I_P and ZX=0. Consequently X³=X.
This is an exact cubic constraint on the surviving corner block,
valid for arbitrary complex matrices without Hermiticity.

For a Hermitian W, the same block identities give an isometry
from the neutral truth sector into the corner sector. This
is the basis for the rank-sensitive 2+2 corner calculation.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The matrix block compressed to the orthogonal complement
of a projection Q. -/
def sixComplementCornerBlock (W Q : SixMat) : SixMat :=
  (1 - Q) * W * (1 - Q)

/-- When a matrix W is involutive and its neutral-neutral block
QWQ is zero, the full complementary block X=(I-Q)W(I-Q)
satisfies X³=X. The proof uses only exact associative ring
identities, not a spectral decomposition or an informal rank
argument. -/
theorem sixMatrix_involution_zeroNeutral_corner_tripotent
    (W Q : SixMat)
    (hW : W * W = 1)
    (hQ : Q * Q = Q)
    (hQQ : Q * W * Q = 0) :
    sixComplementCornerBlock W Q *
        sixComplementCornerBlock W Q *
          sixComplementCornerBlock W Q =
      sixComplementCornerBlock W Q := by
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  have hC_sq : C * C = C := by
    dsimp [C]
    calc
      (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
      _ = 1 - Q := by rw [hQ]; noncomm_ring
  have hCplus : C + Q = 1 := by
    dsimp [C]
    noncomm_ring
  have hCQ : C * Q = 0 := by
    dsimp [C]
    calc
      (1 - Q) * Q = Q - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ]; simp
  have hQC : Q * C = 0 := by
    dsimp [C]
    calc
      Q * (1 - Q) = Q - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ]; simp
  have hQW2 : Q * W * W * C = 0 := by
    calc
      Q * W * W * C = Q * (W * W) * C := by noncomm_ring
      _ = Q * 1 * C := by rw [hW]
      _ = 0 := by simp [hQC]
  have hsplit :
      Q * W * W * C =
        Q * W * C * W * C + (Q * W * Q) * W * C := by
    calc
      Q * W * W * C = Q * W * (C + Q) * W * C := by
        rw [hCplus]
        noncomm_ring
      _ = _ := by noncomm_ring
  have hQWCWC : Q * W * C * W * C = 0 := by
    rw [hQQ] at hsplit
    simp only [zero_mul, add_zero] at hsplit
    exact hsplit.symm.trans hQW2
  have hCW2 : C * W * W * C = C := by
    calc
      C * W * W * C = C * (W * W) * C := by noncomm_ring
      _ = C * 1 * C := by rw [hW]
      _ = C := by simpa using hC_sq
  have hX2 : X * X = C - C * W * Q * W * C := by
    calc
      X * X = C * W * (C * C) * W * C := by
        dsimp [X]
        noncomm_ring
      _ = C * W * C * W * C := by rw [hC_sq]
      _ = C * W * (C + Q) * W * C -
          C * W * Q * W * C := by noncomm_ring
      _ = C * W * W * C - C * W * Q * W * C := by
        rw [hCplus]
        noncomm_ring
      _ = C - C * W * Q * W * C := by rw [hCW2]
  have hX3 : X * X * X = X := by
    calc
      X * X * X = (C - C * W * Q * W * C) * (C * W * C) := by
        rw [hX2]
      _ = C * W * C - C * W * (Q * W * C * W * C) := by
        calc
          _ = (C * C) * W * C -
              C * W * Q * W * (C * C) * W * C := by noncomm_ring
          _ = _ := by rw [hC_sq]; noncomm_ring
      _ = C * W * C := by rw [hQWCWC]; simp
      _ = X := rfl
  exact hX3

/-- Under Hermitianity the columns of an involution are orthonormal.
If the neutral-neutral entries vanish, the sum may be restricted
to the complementary corner sector. -/
theorem sixMatrix_involution_neutralColumns_orthonormal
    (W : SixMat) (neutral : Fin 6 → Prop)
    [DecidablePred neutral]
    (hW : W * W = 1)
    (hHerm : W.IsHermitian)
    (hNN : ∀ i j : Fin 6, neutral i → neutral j → W i j = 0)
    (j k : Fin 6) (hj : neutral j) (hk : neutral k) :
    (∑ i : Fin 6, if ¬neutral i then
      star (W i j) * W i k else 0) =
      if j = k then (1 : ℂ) else 0 := by
  classical
  calc
    (∑ i : Fin 6, if ¬neutral i then
      star (W i j) * W i k else 0) =
        ∑ i : Fin 6, star (W i j) * W i k := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hn : neutral i
      · simp [hn, hNN i k hn hk]
      · simp [hn]
    _ = (W * W) j k := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hHerm.apply j i]
    _ = (1 : SixMat) j k := by rw [hW]
    _ = if j = k then (1 : ℂ) else 0 := by
      simp [Matrix.one_apply]

end Neoplatonic.LTR
