import Neoplatonic.LTR.SixDimensionalSingletonInputGramScalar
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-122: exact operator norm of a singleton neutral transition

MAN-119 identifies KᴴK as a scalar multiple of a singleton
truth-fibre projection N. The scalar is the sum of squared entry
magnitudes of K. Since the Euclidean Hilbert operator norm of N
is one, the C*-identity yields the exact equality

    ||K||_op² = Sum_ij ||K_ij||².

This holds for arbitrary complex six-dimensional K whose input
columns are supported on the one-dimensional truth fibre N.
Applied to K=P_u Y N_v, it identifies each of MAN-117's
transition energies with a genuine squared operator norm.

All matrix norms below use the L² Euclidean operator norm.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The orthogonal coordinate projector onto one labelled
Hilbert basis coordinate has exact Euclidean operator norm one,
independently of the chosen coordinate permutation. -/
theorem sixTruthFibreProjection_singleton_operatorNorm_one
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hMult : truthMultiplicity label u = 1) :
    ‖sixTruthFibreProjection label u‖ = (1 : ℝ) := by
  let v : Fin 6 → ℂ := fun i =>
    if label i = u then (1 : ℂ) else 0
  change ‖(Matrix.diagonal v : SixMat)‖ = (1 : ℝ)
  rw [Matrix.l2_opNorm_diagonal]
  have hle : ‖v‖ ≤ (1 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    by_cases hi : label i = u <;>
      simp [v, hi]
  let s : Finset (Fin 6) := Finset.univ.filter (fun i => label i = u)
  have hcard : s.card = 1 := hMult
  obtain ⟨i, his⟩ := Finset.card_eq_one.mp hcard
  have hi : label i = u := by
    have hmem : i ∈ s := by rw [his]; simp
    exact (Finset.mem_filter.mp hmem).2
  have hge : (1 : ℝ) ≤ ‖v‖ := by
    have h := norm_le_pi_norm v i
    simpa [v, hi] using h
  exact le_antisymm hle hge

/-- For a singleton input truth fibre, the squared Hilbert
operator norm of K equals its squared Frobenius energy.
The six-by-six calculation is exact over the complex field. -/
theorem sixMatrix_singletonInput_opNormSq_eq_entryEnergy
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hMult : truthMultiplicity label u = 1)
    (K : SixMat)
    (hKN : K * sixTruthFibreProjection label u = K) :
    ‖K‖ * ‖K‖ =
      ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2 := by
  let N : SixMat := sixTruthFibreProjection label u
  let e : ℝ := ∑ j : Fin 6, ∑ i : Fin 6, ‖K i j‖ ^ 2
  have he : 0 ≤ e := by
    dsimp [e]
    exact Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have htrace : (K.conjTranspose * K).trace = (e : ℂ) := by
    calc
      (K.conjTranspose * K).trace =
          (K * K.conjTranspose).trace :=
            Matrix.trace_mul_comm K.conjTranspose K
      _ = (e : ℂ) := sixMatrix_gram_trace_eq_entryEnergy K
  have hGram : K.conjTranspose * K = (e : ℂ) • N := by
    have h := sixMatrix_singletonInput_gram_eq_trace_smul_fibre
      label u hMult K hKN
    change K.conjTranspose * K =
      (K.conjTranspose * K).trace • N at h
    rwa [htrace] at h
  have hNnorm : ‖N‖ = (1 : ℝ) :=
    sixTruthFibreProjection_singleton_operatorNorm_one
      label u hMult
  change ‖K‖ * ‖K‖ = e
  calc
    ‖K‖ * ‖K‖ = ‖K.conjTranspose * K‖ :=
      (Matrix.l2_opNorm_conjTranspose_mul_self K).symm
    _ = ‖(e : ℂ) • N‖ := by rw [hGram]
    _ = e := by
      rw [norm_smul, hNnorm, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg he]

end Neoplatonic.LTR
