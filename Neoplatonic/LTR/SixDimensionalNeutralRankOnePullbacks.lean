import Neoplatonic.LTR.SixDimensionalSaturated03TwoDefectChannels
import Mathlib.Tactic

/-!
# LTR-MAN-115: pullback of orthogonal rank-one channels by a partial isometry

In the true saturated six-dimensional Hamming corner, MAN-113 gives
YYᴴ = E0 + E3 with two rank-one output defects. MAN-94 gives
YᴴY = Q, where Q projects to the two-dimensional neutral input sector.

This module proves the coordinate-free algebraic core of the U(2)
input/output transport. Whenever YᴴY=Q and YYᴴ=K0+K3,
with K0,K3 orthogonal trace-one idempotents, then

  F0=YᴴK0Y, F3=YᴴK3Y

are orthogonal rank-one idempotents whose sum is Q.

No basis choice, singular-value decomposition, or normal-form
identification is assumed. The next step is to instantiate K0,K3
with the true opposite-double Dirac Gram defects.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Pullback along a matrix partial isometry preserves an idempotent
K inside its range; trace and rank one are preserved exactly. -/
theorem sixMatrix_rangePullback_rankOne
    (Y E K : SixMat)
    (hRange : Y * Y.conjTranspose = E)
    (hKid : K * K = K)
    (hKE : K * E = K)
    (hKtrace : K.trace = (1 : ℂ)) :
    let F := Y.conjTranspose * K * Y
    F * F = F ∧ F.rank = 1 := by
  dsimp only
  let F : SixMat := Y.conjTranspose * K * Y
  change F * F = F ∧ F.rank = 1
  have hFid : F * F = F := by
    change (Y.conjTranspose * K * Y) *
      (Y.conjTranspose * K * Y) = Y.conjTranspose * K * Y
    calc
      (Y.conjTranspose * K * Y) *
          (Y.conjTranspose * K * Y) =
        Y.conjTranspose *
          (K * (Y * Y.conjTranspose) * K) * Y := by noncomm_ring
      _ = Y.conjTranspose * (K * E * K) * Y := by rw [hRange]
      _ = Y.conjTranspose * (K * K) * Y := by rw [hKE]
      _ = Y.conjTranspose * K * Y := by rw [hKid]
  have hFtrace : F.trace = K.trace := by
    change (Y.conjTranspose * K * Y).trace = K.trace
    calc
      (Y.conjTranspose * K * Y).trace =
          (Y.conjTranspose * (K * Y)).trace := by rw [Matrix.mul_assoc]
      _ = ((K * Y) * Y.conjTranspose).trace :=
        Matrix.trace_mul_comm Y.conjTranspose (K * Y)
      _ = (K * (Y * Y.conjTranspose)).trace := by
        rw [Matrix.mul_assoc]
      _ = K.trace := by rw [hRange, hKE]
  have hRank := sixMatrix_idempotent_trace_eq_rank F hFid
  rw [hFtrace, hKtrace] at hRank
  exact ⟨hFid, by exact_mod_cast hRank.symm⟩

/-- Pulling back two orthogonal trace-one range projections gives
two orthogonal rank-one neutral-sector projections summing exactly
to Q. This is the basis-independent U(2) decomposition. -/
theorem sixMatrix_orthogonalRankOneChannels_pullback
    (Y Q K0 K3 : SixMat)
    (hIso : Y.conjTranspose * Y = Q)
    (hQid : Q * Q = Q)
    (hGram : Y * Y.conjTranspose = K0 + K3)
    (h0id : K0 * K0 = K0)
    (h3id : K3 * K3 = K3)
    (h03 : K0 * K3 = 0)
    (h30 : K3 * K0 = 0)
    (h0trace : K0.trace = (1 : ℂ))
    (h3trace : K3.trace = (1 : ℂ)) :
    let F0 := Y.conjTranspose * K0 * Y
    let F3 := Y.conjTranspose * K3 * Y
    F0 * F0 = F0 ∧ F0.rank = 1 ∧
      F3 * F3 = F3 ∧ F3.rank = 1 ∧
      F0 * F3 = 0 ∧ F3 * F0 = 0 ∧
      F0 + F3 = Q := by
  dsimp only
  let F0 : SixMat := Y.conjTranspose * K0 * Y
  let F3 : SixMat := Y.conjTranspose * K3 * Y
  change F0 * F0 = F0 ∧ F0.rank = 1 ∧
    F3 * F3 = F3 ∧ F3.rank = 1 ∧
    F0 * F3 = 0 ∧ F3 * F0 = 0 ∧ F0 + F3 = Q
  have h0E : K0 * (K0 + K3) = K0 := by
    rw [mul_add, h0id, h03]
    simp
  have h3E : K3 * (K0 + K3) = K3 := by
    rw [mul_add, h30, h3id]
    simp
  obtain ⟨hF0id, hF0rank⟩ :=
    sixMatrix_rangePullback_rankOne
      Y (K0 + K3) K0 hGram h0id h0E h0trace
  obtain ⟨hF3id, hF3rank⟩ :=
    sixMatrix_rangePullback_rankOne
      Y (K0 + K3) K3 hGram h3id h3E h3trace
  exact ⟨hF0id, hF0rank, hF3id, hF3rank, by
    calc
      F0 * F3 =
          Y.conjTranspose *
            (K0 * (Y * Y.conjTranspose) * K3) * Y := by
              dsimp [F0, F3]
              noncomm_ring
      _ = Y.conjTranspose * (K0 * (K0 + K3) * K3) * Y := by
            rw [hGram]
      _ = Y.conjTranspose * (K0 * K3) * Y := by
            rw [h0E]
      _ = 0 := by rw [h03]; simp, by
    calc
      F3 * F0 =
          Y.conjTranspose *
            (K3 * (Y * Y.conjTranspose) * K0) * Y := by
              dsimp [F0, F3]
              noncomm_ring
      _ = Y.conjTranspose * (K3 * (K0 + K3) * K0) * Y := by
            rw [hGram]
      _ = Y.conjTranspose * (K3 * K0) * Y := by
            rw [h3E]
      _ = 0 := by rw [h30]; simp, by
    calc
      F0 + F3 = Y.conjTranspose * (K0 + K3) * Y := by
        dsimp [F0, F3]
        noncomm_ring
      _ = Y.conjTranspose * (Y * Y.conjTranspose) * Y := by
        rw [hGram]
      _ = (Y.conjTranspose * Y) * (Y.conjTranspose * Y) := by
        noncomm_ring
      _ = Q := by rw [hIso, hQid]⟩

end Neoplatonic.LTR
