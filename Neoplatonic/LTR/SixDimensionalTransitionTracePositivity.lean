import Neoplatonic.LTR.SixDimensionalSignedOppositeGram
import Mathlib.Tactic

/-!
# LTR-MAN-118: positivity of fibre-to-fibre neutral exchange traces

For orthogonal truth-sector projectors P and N and any complex
neutral exchange matrix Y, the transition trace

    Tr(P Y N Yᴴ)

is a real nonnegative number. Its value is the squared
Frobenius norm of the restricted matrix K=PYN.

This provides the missing positivity needed to interpret
MAN-117's exact bistochastic 2x2 transition table as a matrix
of physical nonnegative channel energies, while keeping the
original Fin 6 Hilbert coordinates.

The theorem needs only that P,N are Hermitian idempotents.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The trace of a Hermitian projector's double compression
equals the trace of its single-sided compression. -/
theorem sixMatrix_projector_transitionTrace_compression
    (P N Y : SixMat)
    (hP : P * P = P)
    (hPH : P.IsHermitian)
    (hN : N * N = N)
    (hNH : N.IsHermitian) :
    (P * Y * N * Y.conjTranspose).trace =
      ((P * Y * N) * (P * Y * N).conjTranspose).trace := by
  have hGram :
      (P * Y * N) * (P * Y * N).conjTranspose =
        P * Y * N * Y.conjTranspose * P := by
    simp only [Matrix.conjTranspose_mul, hPH.eq, hNH.eq]
    calc
      (P * Y * N) * (N * Y.conjTranspose * P) =
        P * Y * (N * N) * Y.conjTranspose * P := by noncomm_ring
      _ = P * Y * N * Y.conjTranspose * P := by rw [hN]
  calc
    (P * Y * N * Y.conjTranspose).trace =
        (P * Y * N * Y.conjTranspose * P).trace := by
          calc
            _ = (P * (P * Y * N * Y.conjTranspose)).trace :=
              Matrix.trace_mul_comm (P * Y * N * Y.conjTranspose) P
            _ = ((P * P) * Y * N * Y.conjTranspose).trace := by
              congr 1
              noncomm_ring
            _ = (P * Y * N * Y.conjTranspose).trace := by rw [hP]
    _ = ((P * Y * N) * (P * Y * N).conjTranspose).trace := by
      rw [hGram]

/-- A transition trace is the complex coercion of a sum of
squared entry norms and hence is real and nonnegative. -/
theorem sixMatrix_projector_transitionTrace_nonneg
    (P N Y : SixMat)
    (hP : P * P = P)
    (hPH : P.IsHermitian)
    (hN : N * N = N)
    (hNH : N.IsHermitian) :
    ∃ e : ℝ, 0 ≤ e ∧
      (P * Y * N * Y.conjTranspose).trace = (e : ℂ) := by
  let K : SixMat := P * Y * N
  let e : ℝ := ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2
  have hTrace :
      (P * Y * N * Y.conjTranspose).trace = (e : ℂ) := by
    calc
      (P * Y * N * Y.conjTranspose).trace =
          (K * K.conjTranspose).trace := by
            exact sixMatrix_projector_transitionTrace_compression
              P N Y hP hPH hN hNH
      _ = (e : ℂ) := sixMatrix_gram_trace_eq_entryEnergy K
  refine ⟨e, ?_, hTrace⟩
  dsimp [e]
  exact Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun i _ => sq_nonneg _))

/-- The imaginary part of a transition trace between Hermitian
idempotent truth-sector projectors vanishes. -/
theorem sixMatrix_projector_transitionTrace_im_zero
    (P N Y : SixMat)
    (hP : P * P = P)
    (hPH : P.IsHermitian)
    (hN : N * N = N)
    (hNH : N.IsHermitian) :
    ((P * Y * N * Y.conjTranspose).trace).im = 0 := by
  obtain ⟨e, _, he⟩ :=
    sixMatrix_projector_transitionTrace_nonneg P N Y hP hPH hN hNH
  rw [he]
  simp

/-- The real part of every projector transition trace is
nonnegative in the original labelled complex matrix chart. -/
theorem sixMatrix_projector_transitionTrace_re_nonneg
    (P N Y : SixMat)
    (hP : P * P = P)
    (hPH : P.IsHermitian)
    (hN : N * N = N)
    (hNH : N.IsHermitian) :
    0 ≤ ((P * Y * N * Y.conjTranspose).trace).re := by
  obtain ⟨e, he_nonneg, he⟩ :=
    sixMatrix_projector_transitionTrace_nonneg P N Y hP hPH hN hNH
  rw [he]
  simpa using he_nonneg

end Neoplatonic.LTR
