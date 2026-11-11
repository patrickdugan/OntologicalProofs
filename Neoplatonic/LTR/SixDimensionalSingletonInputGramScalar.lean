import Neoplatonic.LTR.SixDimensionalSaturatedRankOneBlocks
import Neoplatonic.LTR.SixDimensionalSignedOppositeGram
import Mathlib.Tactic

/-!
# LTR-MAN-119: singleton-input Gram matrices are scalar projectors

For a labelled finite six-dimensional Hilbert space, let
N_u be the diagonal projection onto a truth fibre of
multiplicity one. Any matrix K satisfying K N_u = K has
only a single potentially nonzero input column.

The exact Gram matrix KᴴK therefore equals its trace
times N_u. The statement holds for arbitrary complex
entries and is invariant under permutations of the six
original Dirac coordinates.

This is a basis-free input-channel norm bridge for
MAN-117's neutral transition energies: the Gram matrix
of P_u Y N_v has just one nonzero eigenvalue, equal to
its squared Frobenius energy.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A matrix supported on one truth-fibre input column has
its Gram operator equal to its trace times that fibre's
rank-one coordinate projection. -/
theorem sixMatrix_singletonInput_gram_eq_trace_smul_fibre
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hMult : truthMultiplicity label u = 1)
    (K : SixMat)
    (hKN : K * sixTruthFibreProjection label u = K) :
    let N := sixTruthFibreProjection label u
    K.conjTranspose * K =
      ((K.conjTranspose * K).trace : ℂ) • N := by
  dsimp only
  let N : SixMat := sixTruthFibreProjection label u
  let H : SixMat := K.conjTranspose * K
  change H = H.trace • N
  have hColumnZero (i j : Fin 6) (hj : label j ≠ u) :
      K i j = 0 := by
    have h := congrArg (fun M : SixMat => M i j) hKN
    simpa [sixTruthFibreProjection, Matrix.mul_diagonal, hj] using h.symm
  have hRowZero (i j : Fin 6) (hi : label i ≠ u) :
      H i j = 0 := by
    dsimp only [H]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Matrix.conjTranspose_apply, hColumnZero k i hi]
    simp
  have hColZero (i j : Fin 6) (hj : label j ≠ u) :
      H i j = 0 := by
    dsimp only [H]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k hk
    rw [hColumnZero k j hj]
    simp
  have hTraceAt (i : Fin 6) (hi : label i = u) :
      H.trace = H i i := by
    change (∑ k : Fin 6, H k k) = H i i
    apply Finset.sum_eq_single i
    · intro k hk hki
      by_cases hku : label k = u
      · have heq :=
          sixTruthFibreMultiplicity_one_unique label u hMult k i hku hi
        exact (hki heq).elim
      · exact hRowZero k k hku
    · simp
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : label i = u
    · have ht := hTraceAt i hi
      simp [N, sixTruthFibreProjection, Matrix.smul_apply,
        Matrix.diagonal_apply, hi, ht]
    · have hz := hRowZero i i hi
      simp [N, sixTruthFibreProjection, Matrix.smul_apply,
        Matrix.diagonal_apply, hi, hz]
  · have hz : H i j = 0 := by
      by_cases hi : label i = u
      · by_cases hj : label j = u
        · exact False.elim
            (hij (sixTruthFibreMultiplicity_one_unique
              label u hMult i j hi hj))
        · exact hColZero i j hj
      · exact hRowZero i j hi
    simp [N, sixTruthFibreProjection, Matrix.smul_apply,
      Matrix.diagonal_apply, hij, hz]

/-- The scalar coefficient of a singleton-input Gram is a
nonnegative real number, equal to the sum of squared moduli
of the original six-dimensional matrix entries. -/
theorem sixMatrix_singletonInput_gram_nonnegativeScalar
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hMult : truthMultiplicity label u = 1)
    (K : SixMat)
    (hKN : K * sixTruthFibreProjection label u = K) :
    ∃ e : ℝ, 0 ≤ e ∧
      K.conjTranspose * K =
        (e : ℂ) • sixTruthFibreProjection label u := by
  let e : ℝ := ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2
  have htrace : (K.conjTranspose * K).trace = (e : ℂ) := by
    calc
      (K.conjTranspose * K).trace =
          (K * K.conjTranspose).trace :=
            Matrix.trace_mul_comm K.conjTranspose K
      _ = (e : ℂ) := sixMatrix_gram_trace_eq_entryEnergy K
  refine ⟨e, ?_, ?_⟩
  · dsimp [e]
    exact Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun i _ => sq_nonneg _))
  · have h := sixMatrix_singletonInput_gram_eq_trace_smul_fibre
      label u hMult K hKN
    change K.conjTranspose * K =
      (K.conjTranspose * K).trace • sixTruthFibreProjection label u at h
    rwa [htrace] at h

end Neoplatonic.LTR
