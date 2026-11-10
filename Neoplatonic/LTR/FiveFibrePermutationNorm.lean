import Neoplatonic.LTR.FiveFibreCanonicalPermutation
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-41: Hilbert operator norm and commutator invariance under truth-chart permutations

For any σ : Equiv.Perm (Fin 5), the simultaneously permuted matrix
D.submatrix σ σ is conjugate to D by the two inverse permutation
matrices. Each permutation matrix has complex ℓ² operator norm one.
Submultiplicativity, applied in both directions, proves that
simultaneous row/column permutation preserves the genuine Hilbert
operator norm.

Commutation with a represented diagonal observable transforms
covariantly: [D^σ,diag(f∘σ)] = [D,diag(f)]^σ. The corresponding
continuous Hilbert operator norms are therefore exactly equal.

This supplies the analytic component of the diagonal-label change of
basis needed to transport arbitrary faithful five-dimensional truth
representations into the canonical chart.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private theorem fiveFibre_permMatrix_mul_left
    (σ : Equiv.Perm (Fin 5))
    (M : Matrix (Fin 5) (Fin 5) ℂ) (i j : Fin 5) :
    (σ.permMatrix ℂ * M) i j = M (σ i) j := by
  change ((σ.permMatrix ℂ) *ᵥ (fun k => M k j)) i = _
  rw [Matrix.permMatrix_mulVec]
  rfl

private theorem fiveFibre_permMatrix_mul_right
    (σ : Equiv.Perm (Fin 5))
    (M : Matrix (Fin 5) (Fin 5) ℂ) (i j : Fin 5) :
    (M * σ.symm.permMatrix ℂ) i j = M i (σ j) := by
  change ((fun k => M i k) ᵥ* (σ.symm.permMatrix ℂ)) j = _
  rw [Matrix.vecMul_permMatrix]
  rfl

/-- Simultaneous permutation of both matrix axes is conjugation by
inverse permutation matrices. -/
theorem fiveFibre_submatrix_eq_permutationConjugation
    (σ : Equiv.Perm (Fin 5))
    (M : Matrix (Fin 5) (Fin 5) ℂ) :
    M.submatrix σ σ =
      σ.permMatrix ℂ * M * σ.symm.permMatrix ℂ := by
  ext i j
  change M (σ i) (σ j) = _
  rw [fiveFibre_permMatrix_mul_right σ
    (σ.permMatrix ℂ * M) i j]
  exact (fiveFibre_permMatrix_mul_left σ M i (σ j)).symm

private theorem fiveFibre_submatrix_opNorm_le
    (σ : Equiv.Perm (Fin 5))
    (M : Matrix (Fin 5) (Fin 5) ℂ) :
    ‖M.submatrix σ σ‖ ≤ ‖M‖ := by
  have hp : ‖σ.permMatrix ℂ‖ = 1 :=
    Matrix.permMatrix_l2_opNorm_eq σ
  have hq : ‖σ.symm.permMatrix ℂ‖ = 1 :=
    Matrix.permMatrix_l2_opNorm_eq σ.symm
  rw [fiveFibre_submatrix_eq_permutationConjugation]
  calc
    ‖σ.permMatrix ℂ * M * σ.symm.permMatrix ℂ‖ ≤
        ‖σ.permMatrix ℂ * M‖ * ‖σ.symm.permMatrix ℂ‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖σ.permMatrix ℂ‖ * ‖M‖) *
        ‖σ.symm.permMatrix ℂ‖ :=
      mul_le_mul_of_nonneg_right
        (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖M‖ := by rw [hp, hq]; ring

/-- Conjugation by a permutation is an isometry for the genuine
complex Euclidean Hilbert operator norm of a finite matrix. -/
theorem fiveFibre_submatrix_opNorm_eq
    (σ : Equiv.Perm (Fin 5))
    (M : Matrix (Fin 5) (Fin 5) ℂ) :
    ‖M.submatrix σ σ‖ = ‖M‖ := by
  apply le_antisymm
  · exact fiveFibre_submatrix_opNorm_le σ M
  · have hback :
        (M.submatrix σ σ).submatrix σ.symm σ.symm = M := by
      ext i j
      simp [Matrix.submatrix_apply]
    calc
      ‖M‖ = ‖(M.submatrix σ σ).submatrix σ.symm σ.symm‖ := by
        rw [hback]
      _ ≤ ‖M.submatrix σ σ‖ :=
        fiveFibre_submatrix_opNorm_le σ.symm (M.submatrix σ σ)

/-- The literal matrix commutator with a diagonal truth observable
is equivariant under a simultaneous Hilbert-coordinate permutation. -/
theorem fiveFibre_permutedDiracComm_matrix
    (σ : Equiv.Perm (Fin 5))
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Fin 5 → ℂ) :
    (D.submatrix σ σ) * Matrix.diagonal (f ∘ σ) -
      Matrix.diagonal (f ∘ σ) * (D.submatrix σ σ) =
    (D * Matrix.diagonal f - Matrix.diagonal f * D).submatrix σ σ := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.submatrix_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Function.comp_apply]

/-- The genuine continuous Hilbert-space operator norm of the Dirac
commutator is invariant under simultaneous Hilbert-coordinate
permutation, with the observable values permuted accordingly. -/
theorem fiveFibre_permutedDiracComm_norm
    (σ : Equiv.Perm (Fin 5))
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Fin 5 → ℂ) :
    ‖((D.submatrix σ σ) * Matrix.diagonal (f ∘ σ) -
       Matrix.diagonal (f ∘ σ) * (D.submatrix σ σ)
      ).toEuclideanLin.toContinuousLinearMap‖ =
    ‖(D * Matrix.diagonal f -
       Matrix.diagonal f * D
      ).toEuclideanLin.toContinuousLinearMap‖ := by
  rw [fiveFibre_permutedDiracComm_matrix]
  change ‖(D * Matrix.diagonal f -
      Matrix.diagonal f * D).submatrix σ σ‖ =
    ‖D * Matrix.diagonal f - Matrix.diagonal f * D‖
  exact fiveFibre_submatrix_opNorm_eq σ _

end Neoplatonic.LTR
