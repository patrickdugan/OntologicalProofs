import Neoplatonic.LTR.SixDimensionalSignedOppositeGram
import Mathlib.Tactic

/-!
# LTR-MAN-118: positivity of fibre-to-fibre transition traces

MAN-117 expresses the true saturated neutral-exchange amplitudes
by the 2x2 table Tr(P_u Y N_v Yᴴ). The remaining numerical
argument needs their positivity and realness, which follow from
the fact that each entry is the Gram trace of P_u Y N_v.

The present finite-complex lemma works with arbitrary Hermitian
idempotents P,N, and arbitrary six-dimensional Y. Its conclusion
is a real sum of squared absolute entry norms.

It is basis-independent and uses the original complex matrix
coordinates. No canonical U(2) basis is chosen.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A compression transition trace is a Frobenius Gram trace:
Tr(P Y N Yᴴ) = Tr((P Y N)(P Y N)ᴴ). -/
theorem sixMatrix_transitionTrace_eq_gramTrace
    (P N Y : SixMat)
    (hPid : P * P = P)
    (hNid : N * N = N)
    (hPH : P.IsHermitian)
    (hNH : N.IsHermitian) :
    (P * Y * N * Y.conjTranspose).trace =
      ((P * Y * N) * (P * Y * N).conjTranspose).trace := by
  have heq : (P * Y * N) * (P * Y * N).conjTranspose =
      P * Y * N * Y.conjTranspose * P := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hPH.eq, hNH.eq]
    calc
      (P * Y * N) * (N * (Y.conjTranspose * P)) =
        P * Y * (N * N) * Y.conjTranspose * P := by noncomm_ring
      _ = P * Y * N * Y.conjTranspose * P := by rw [hNid]
  rw [heq]
  have hrewrite : P * (P * Y * N * Y.conjTranspose) =
      P * Y * N * Y.conjTranspose := by
    calc
      P * (P * Y * N * Y.conjTranspose) =
          (P * P) * Y * N * Y.conjTranspose := by noncomm_ring
      _ = P * Y * N * Y.conjTranspose := by rw [hPid]
  calc
    (P * Y * N * Y.conjTranspose).trace =
        (P * (P * Y * N * Y.conjTranspose)).trace := by rw [hrewrite]
    _ = ((P * Y * N * Y.conjTranspose) * P).trace :=
      Matrix.trace_mul_comm P (P * Y * N * Y.conjTranspose)
    _ = (P * Y * N * Y.conjTranspose * P).trace := rfl

/-- The compressed transition trace is the complex embedding of
a nonnegative real sum of squared entry norms. -/
theorem sixMatrix_transitionTrace_nonnegativeReal
    (P N Y : SixMat)
    (hPid : P * P = P)
    (hNid : N * N = N)
    (hPH : P.IsHermitian)
    (hNH : N.IsHermitian) :
    ∃ e : ℝ, 0 ≤ e ∧
      (P * Y * N * Y.conjTranspose).trace = (e : ℂ) := by
  let B : SixMat := P * Y * N
  let e : ℝ := ∑ j : Fin 6, ∑ i : Fin 6, ‖B i j‖ ^ 2
  refine ⟨e, ?_, ?_⟩
  · dsimp [e]
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro i hi
    positivity
  · calc
      (P * Y * N * Y.conjTranspose).trace =
          (B * B.conjTranspose).trace :=
        sixMatrix_transitionTrace_eq_gramTrace P N Y
          hPid hNid hPH hNH
      _ = (e : ℂ) := by
        exact sixMatrix_gram_trace_eq_entryEnergy B

/-- A nonnegative real 2x2 row of total one contains an entry
at most a half, the scalar gate for the canonical norm no-go. -/
theorem twoTransitionNonnegative_rowHalf
    (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsum : a + b = 1) :
    a ≤ (1 / 2 : ℝ) ∨ b ≤ (1 / 2 : ℝ) := by
  by_contra h
  push_neg at h
  rcases h with ⟨ha', hb'⟩
  linarith

/-- Nonnegative entries of a doubly stochastic 2x2 table lie
in the unit interval and obey a half-energy dichotomy. -/
theorem twoTransitionNonnegative_bistochastic_bounds
    (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hr0 : a + b = 1)
    (hr1 : c + d = 1)
    (hc0 : a + c = 1)
    (hc1 : b + d = 1) :
    (a ≤ 1 ∧ b ≤ 1 ∧ c ≤ 1 ∧ d ≤ 1) ∧
      (a = d ∧ b = c) ∧
      (a ≤ (1 / 2 : ℝ) ∨ b ≤ (1 / 2 : ℝ)) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · exact twoTransitionNonnegative_rowHalf a b ha hb hr0

end Neoplatonic.LTR
