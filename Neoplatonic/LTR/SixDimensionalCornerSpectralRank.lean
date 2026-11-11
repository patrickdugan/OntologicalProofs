import Neoplatonic.LTR.SixDimensionalSignedWitnessPartialIsometry
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# LTR-MAN-94: corner trace and rank at a two-dimensional neutral sector

MAN-94's full involution block equation X²+YZ=C, combined with
the cyclic matrix trace and ZY=Q, fixes the corner square trace:

       Tr(X²) = 6 - 2 Tr(Q).

MAN-93 proves X³=X. Thus E=X² is idempotent. In a finite
complex vector space the trace of an idempotent equals the
complex dimension of its image. In particular, when Tr(Q)=2
the true six-dimensional corner compression X has rank two.

The final rank equality uses X³=X to show rank(X)=rank(X²),
so the argument is independent of diagonalizability lemmas,
coordinate permutations, or any assumption on fibre multiplicity.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The corner square trace in an arbitrary neutral-zero
six-dimensional matrix involution is 6-2 times the neutral
projector trace. -/
theorem sixMatrix_involution_zeroNeutral_cornerSquare_trace
    (W Q : SixMat) (hW : W * W = 1)
    (hQ : Q * Q = Q) (hQQ : Q * W * Q = 0) :
    ((sixComplementCornerBlock W Q) *
      (sixComplementCornerBlock W Q)).trace =
        (6 : ℂ) - 2 * Q.trace := by
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Z : SixMat := Q * W * C
  have hbase :=
    sixMatrix_involution_zeroNeutral_fullBlockEquations W Q hW hQ hQQ
  change X * X + Y * Z = C ∧
    X * Y = 0 ∧ Z * X = 0 ∧ Z * Y = Q at hbase
  obtain ⟨hX, _, _, hZY⟩ := hbase
  have htrace : (X * X).trace + (Y * Z).trace = C.trace := by
    simpa only [Matrix.trace_add] using congrArg Matrix.trace hX
  have hcyc : (Y * Z).trace = Q.trace := by
    rw [Matrix.trace_mul_comm, hZY]
  have hCtrace : C.trace = (6 : ℂ) - Q.trace := by
    dsimp [C]
    rw [Matrix.trace_sub, Matrix.trace_one]
    norm_num
  rw [hcyc, hCtrace] at htrace
  change (X * X).trace = (6 : ℂ) - 2 * Q.trace
  linear_combination htrace

/-- The square of a tripotent complex matrix is idempotent. -/
theorem sixMatrix_tripotent_square_idempotent
    (X : SixMat) (h : X * X * X = X) :
    (X * X) * (X * X) = X * X := by
  calc
    (X * X) * (X * X) = (X * X * X) * X := by noncomm_ring
    _ = X * X := by rw [h]

/-- In finite complex coordinates, the trace of any idempotent
matrix equals its matrix rank, using the actual endomorphism
range and Mathlib's idempotent-projection trace theorem. -/
theorem sixMatrix_idempotent_trace_eq_rank
    (M : SixMat) (h : M * M = M) :
    M.trace = (M.rank : ℂ) := by
  let e : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) := M.toLin'
  have he : IsIdempotentElem e := by
    change e ∘ₗ e = e
    simpa only [e, Matrix.toLin'_mul] using congrArg Matrix.toLin' h
  have htr := (IsIdempotentElem.isProj_range e he).trace
  change LinearMap.trace ℂ (Fin 6 → ℂ) e =
    (Module.finrank ℂ (LinearMap.range e) : ℂ) at htr
  simpa [e, Matrix.trace_toLin'_eq, Matrix.rank] using htr

/-- If the neutral projection of a six-dimensional involution
has trace two, the complementary corner matrix X has exactly
rank two. Its square is itself an idempotent of rank two. -/
theorem sixMatrix_involution_neutralTraceTwo_cornerRankTwo
    (W Q : SixMat) (hW : W * W = 1)
    (hQ : Q * Q = Q) (hQQ : Q * W * Q = 0)
    (hTrace : Q.trace = (2 : ℂ)) :
    (sixComplementCornerBlock W Q).rank = 2 ∧
      ((sixComplementCornerBlock W Q) *
        (sixComplementCornerBlock W Q)).rank = 2 := by
  let X : SixMat := sixComplementCornerBlock W Q
  change X.rank = 2 ∧ (X * X).rank = 2
  have hX3 : X * X * X = X :=
    sixMatrix_involution_zeroNeutral_corner_tripotent W Q hW hQ hQQ
  have hX2id := sixMatrix_tripotent_square_idempotent X hX3
  have htr : (X * X).trace = (2 : ℂ) := by
    have h :=
      sixMatrix_involution_zeroNeutral_cornerSquare_trace W Q hW hQ hQQ
    change (X * X).trace = (6 : ℂ) - 2 * Q.trace at h
    rw [hTrace] at h
    norm_num at h ⊢
    exact h
  have hrankSq : (X * X).rank = 2 := by
    have hRankEq := sixMatrix_idempotent_trace_eq_rank
      (X * X) hX2id
    rw [htr] at hRankEq
    exact_mod_cast hRankEq.symm
  have hle : X.rank ≤ (X * X).rank := by
    calc
      X.rank = (X * X * X).rank := congrArg Matrix.rank hX3.symm
      _ ≤ (X * X).rank := Matrix.rank_mul_le_left (X * X) X
  have hle' : (X * X).rank ≤ X.rank := Matrix.rank_mul_le_left X X
  have hrankX : X.rank = (X * X).rank := le_antisymm hle hle'
  exact ⟨hrankX.trans hrankSq, hrankSq⟩

end Neoplatonic.LTR
