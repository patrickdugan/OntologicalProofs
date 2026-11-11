import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-120: exact norm gate for orthogonal Hermitian channels

The remaining positive-saturation (2,1,1,2) candidate from MAN-112
has an active opposite-atom channel of operator norm 1/2 and
two neutral-exchange channels. MAN-113/115 construct their
one-dimensional complementary range and pullback projections,
while MAN-117/118 identify a bistochastic table of their
nonnegative squared coupling magnitudes.

A crucial basis-free analytic step is an exact C*-algebra
identity: Hermitian matrices whose products vanish have the
norm of their sum equal to the maximum of their separate norms.
This follows directly from the Mathlib normal-element norm
theorem, using the actual L2 Euclidean operator norm on 6x6
complex matrices.

The resulting three-channel theorem says that a 1/2-sized
opposite coupling and two mutually orthogonal channels with
squared norms <= 1/2 always produce an operator of norm < 1.
This is the reusable norm gate needed to contradict MAN-74's
coordinate-commutator norm lower bound under exact Hamming.

A future proof must derive these channel decompositions and
orthogonality identities for the *actual* labelled coordinate
commutators. No complete six-dimensional no-go is claimed here.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- An orthogonal pair of Hermitian six-dimensional matrices
has sum norm equal to the maximum of the two separate norms. -/
theorem sixMatrix_orthogonalHermitian_norm_add_eq_max
    (A B : SixMat)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A * B = 0) :
    ‖A + B‖ = max ‖A‖ ‖B‖ := by
  have hA' : IsSelfAdjoint A :=
    (Matrix.isHermitian_iff_isSelfAdjoint).mp hA
  have hB' : IsSelfAdjoint B :=
    (Matrix.isHermitian_iff_isSelfAdjoint).mp hB
  exact hA'.norm_add_eq_max hB' hAB

/-- Three pairwise orthogonal Hermitian channels have norm equal
to the maximum of their component Euclidean operator norms. -/
theorem sixMatrix_threeOrthogonalHermitian_norm_eq_max
    (A B C : SixMat)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hC : C.IsHermitian)
    (hAB : A * B = 0)
    (hAC : A * C = 0)
    (hBC : B * C = 0) :
    ‖A + B + C‖ = max (max ‖A‖ ‖B‖) ‖C‖ := by
  have hABHerm : (A + B).IsHermitian := hA.add hB
  have hABC : (A + B) * C = 0 := by
    rw [add_mul, hAC, hBC]
    simp
  calc
    ‖A + B + C‖ =
        max ‖A + B‖ ‖C‖ :=
      sixMatrix_orthogonalHermitian_norm_add_eq_max
        (A + B) C hABHerm hC hABC
    _ = max (max ‖A‖ ‖B‖) ‖C‖ := by
      rw [sixMatrix_orthogonalHermitian_norm_add_eq_max
        A B hA hB hAB]

/-- An active channel bounded by 1/2 together with two
orthogonal Hermitian channels of squared norm at most 1/2
has strictly subunit operator norm. -/
theorem sixMatrix_threeOrthogonalHermitian_halfEnergy_norm_lt_one
    (H L M : SixMat)
    (hH : H.IsHermitian) (hL : L.IsHermitian)
    (hM : M.IsHermitian)
    (hHL : H * L = 0)
    (hHM : H * M = 0)
    (hLM : L * M = 0)
    (hHbound : ‖H‖ ≤ (1 / 2 : ℝ))
    (hLbound : ‖L‖ * ‖L‖ ≤ (1 / 2 : ℝ))
    (hMbound : ‖M‖ * ‖M‖ ≤ (1 / 2 : ℝ)) :
    ‖H + L + M‖ < (1 : ℝ) := by
  have hh : ‖H‖ < (1 : ℝ) := by linarith
  have hl : ‖L‖ < (1 : ℝ) := by
    nlinarith [norm_nonneg L]
  have hm : ‖M‖ < (1 : ℝ) := by
    nlinarith [norm_nonneg M]
  rw [sixMatrix_threeOrthogonalHermitian_norm_eq_max
    H L M hH hL hM hHL hHM hLM]
  exact max_lt (max_lt hh hl) hm

/-- A three-channel Hermitian decomposition with those bounds
contradicts any independent unit-norm lower bound. -/
theorem sixMatrix_threeOrthogonalHermitian_unitNorm_obstruction
    (H L M : SixMat)
    (hH : H.IsHermitian) (hL : L.IsHermitian)
    (hM : M.IsHermitian)
    (hHL : H * L = 0)
    (hHM : H * M = 0)
    (hLM : L * M = 0)
    (hHbound : ‖H‖ ≤ (1 / 2 : ℝ))
    (hLbound : ‖L‖ * ‖L‖ ≤ (1 / 2 : ℝ))
    (hMbound : ‖M‖ * ‖M‖ ≤ (1 / 2 : ℝ))
    (hUnit : (1 : ℝ) ≤ ‖H + L + M‖) :
    False := by
  have hlt := sixMatrix_threeOrthogonalHermitian_halfEnergy_norm_lt_one
    H L M hH hL hM hHL hHM hLM hHbound hLbound hMbound
  linarith

end Neoplatonic.LTR
