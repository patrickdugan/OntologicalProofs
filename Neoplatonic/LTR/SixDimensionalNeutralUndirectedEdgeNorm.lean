import Neoplatonic.LTR.SixDimensionalOffDiagonalNeutralEdgeOrthogonality
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-128: norm of an undirected corner-neutral edge

For Hermitian orthogonal truth-fibre projectors P,N, put K=PYN.
The corresponding undirected edge is E=PYN+NYᴴP=K+Kᴴ.

The oriented channels satisfy K²=(Kᴴ)²=0. Therefore
 EᴴE=KKᴴ+KᴴK,
with orthogonal Hermitian Gram summands. By the C*-norm maximum
identity and the complex Hilbert operator C*-identity,

   ||E||² = ||K||².

This basis-free result applies directly in the actual six-coordinate
Dirac chart. Later MAN-122 will turn ||K||² into the transition
trace energy of a singleton neutral input fibre.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- An undirected Hermitian edge between orthogonal truth fibres
has exactly the same squared operator norm as its oriented block. -/
theorem sixMatrix_neutralUndirectedEdge_normSq_eq_orientedNormSq
    (P N Y : SixMat)
    (hPH : P.IsHermitian) (hNH : N.IsHermitian)
    (hPN : P * N = 0) (hNP : N * P = 0) :
    ‖sixMatrix_neutralUndirectedEdge P N Y‖ *
        ‖sixMatrix_neutralUndirectedEdge P N Y‖ =
      ‖P * Y * N‖ * ‖P * Y * N‖ := by
  let K : SixMat := P * Y * N
  let E : SixMat := sixMatrix_neutralUndirectedEdge P N Y
  change ‖E‖ * ‖E‖ = ‖K‖ * ‖K‖
  have hE : E = K + K.conjTranspose := by
    change P * Y * N + N * Y.conjTranspose * P =
      P * Y * N + (P * Y * N).conjTranspose
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hPH.eq, hNH.eq]
    noncomm_ring
  have hK2 : K * K = 0 := by
    change (P * Y * N) * (P * Y * N) = 0
    calc
      (P * Y * N) * (P * Y * N) =
          P * Y * (N * P) * Y * N := by noncomm_ring
      _ = 0 := by rw [hNP]; simp
  have hKs2 : K.conjTranspose * K.conjTranspose = 0 := by
    have h := congrArg Matrix.conjTranspose hK2
    simpa only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_zero] using h
  have hG1 : (K * K.conjTranspose).IsHermitian := by
    change (K * K.conjTranspose).conjTranspose =
      K * K.conjTranspose
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hG2 : (K.conjTranspose * K).IsHermitian := by
    change (K.conjTranspose * K).conjTranspose =
      K.conjTranspose * K
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hG12 :
      (K * K.conjTranspose) * (K.conjTranspose * K) = 0 := by
    calc
      (K * K.conjTranspose) * (K.conjTranspose * K) =
          K * (K.conjTranspose * K.conjTranspose) * K := by
            noncomm_ring
      _ = 0 := by rw [hKs2]; simp
  have hEsq :
      E.conjTranspose * E =
        K * K.conjTranspose + K.conjTranspose * K := by
    rw [hE]
    have hEH :
        (K + K.conjTranspose).conjTranspose =
          K + K.conjTranspose := by
      rw [Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose]
      abel
    rw [hEH]
    calc
      (K + K.conjTranspose) * (K + K.conjTranspose) =
          K * K + K * K.conjTranspose +
            K.conjTranspose * K +
            K.conjTranspose * K.conjTranspose := by noncomm_ring
      _ = K * K.conjTranspose + K.conjTranspose * K := by
        rw [hK2, hKs2]
        abel
  have hG1Norm :
      ‖K * K.conjTranspose‖ = ‖K‖ * ‖K‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self K.conjTranspose
    simpa only [Matrix.conjTranspose_conjTranspose,
      Matrix.l2_opNorm_conjTranspose] using h
  have hG2Norm :
      ‖K.conjTranspose * K‖ = ‖K‖ * ‖K‖ :=
    Matrix.l2_opNorm_conjTranspose_mul_self K
  have hSA : IsSelfAdjoint (K * K.conjTranspose) :=
    Matrix.isHermitian_iff_isSelfAdjoint.mp hG1
  have hSB : IsSelfAdjoint (K.conjTranspose * K) :=
    Matrix.isHermitian_iff_isSelfAdjoint.mp hG2
  calc
    ‖E‖ * ‖E‖ = ‖E.conjTranspose * E‖ :=
      (Matrix.l2_opNorm_conjTranspose_mul_self E).symm
    _ = ‖K * K.conjTranspose + K.conjTranspose * K‖ := by
      rw [hEsq]
    _ = max ‖K * K.conjTranspose‖
          ‖K.conjTranspose * K‖ :=
      hSA.norm_add_eq_max hSB hG12
    _ = ‖K‖ * ‖K‖ := by
      rw [hG1Norm, hG2Norm, max_self]

end Neoplatonic.LTR
