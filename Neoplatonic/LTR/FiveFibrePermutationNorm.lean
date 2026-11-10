import Neoplatonic.LTR.FiveFibreChartPermutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Tactic

/-!
# LTR-MAN-41: Hilbert operator norms invariant under basis permutation

A bijection of the five Hilbert basis coordinates reindexes a complex
matrix simultaneously in its rows and columns. This is a genuine
star-algebra automorphism of the matrix algebra.

The complex matrix C*-norm is precisely the operator norm of the
associated bounded operator on the five-dimensional Euclidean Hilbert
space. Every star-algebra equivalence between C*-algebras is isometric,
so the actual commutator operator norm is unchanged by coordinate
permutation.

We also certify that reindexing commutes with matrix multiplication,
subtraction and diagonal observable representation. These identities
will transport the full Connes dual metric to the canonical chart.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

/-- Simultaneous row/column reindexing is a star-algebra
equivalence of complex five-by-five matrix algebras. -/
def fiveFibre_reindexStarAlgEquiv (e : Fin 5 ≃ Fin 5) :
    Matrix (Fin 5) (Fin 5) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin 5) (Fin 5) ℂ :=
  StarAlgEquiv.ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    intro M
    ext i j
    simp [Matrix.reindex_apply, Matrix.conjTranspose_apply])

/-- A coordinate permutation preserves the actual continuous
Hilbert-space operator norm of every complex matrix. -/
theorem fiveFibre_reindex_operatorNorm
    (e : Fin 5 ≃ Fin 5) (M : Matrix (Fin 5) (Fin 5) ℂ) :
    ‖(Matrix.reindex e e M).toEuclideanLin.toContinuousLinearMap‖ =
      ‖M.toEuclideanLin.toContinuousLinearMap‖ := by
  have h := StarAlgEquiv.norm_map (fiveFibre_reindexStarAlgEquiv e) M
  simpa only [fiveFibre_reindexStarAlgEquiv,
    StarAlgEquiv.ofAlgEquiv_apply,
    Matrix.coe_reindexAlgEquiv, Matrix.l2_opNorm_def] using h

/-- A diagonal represented truth observable reindexes by
precomposing its values with the inverse coordinate permutation. -/
theorem fiveFibre_reindex_diagonal
    (e : Fin 5 ≃ Fin 5) (f : Fin 5 → ℂ) :
    Matrix.reindex e e (Matrix.diagonal f) =
      Matrix.diagonal (fun i => f (e.symm i)) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.diagonal_apply]

/-- Reindexing a Dirac matrix and a truth observable produces
the same literal commutator as reindexing their commutator. -/
theorem fiveFibre_reindex_commutator
    (e : Fin 5 ≃ Fin 5)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Fin 5 → ℂ) :
    Matrix.reindex e e
      (D * Matrix.diagonal f - Matrix.diagonal f * D) =
      (Matrix.reindex e e D) *
        Matrix.diagonal (fun i => f (e.symm i)) -
      Matrix.diagonal (fun i => f (e.symm i)) *
        (Matrix.reindex e e D) := by
  have h := map_sub (Matrix.reindexRingEquiv ℂ e)
    (D * Matrix.diagonal f) (Matrix.diagonal f * D)
  simpa only [Matrix.coe_reindexRingEquiv, map_mul,
    fiveFibre_reindex_diagonal] using h

/-- Under a simultaneous permutation of Hilbert coordinates,
every represented observable has precisely the same actual Dirac
commutator norm. -/
theorem fiveFibre_reindex_commutator_norm
    (e : Fin 5 ≃ Fin 5)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Fin 5 → ℂ) :
    ‖(((Matrix.reindex e e D) *
        Matrix.diagonal (fun i => f (e.symm i)) -
       Matrix.diagonal (fun i => f (e.symm i)) *
        (Matrix.reindex e e D)).toEuclideanLin.toContinuousLinearMap)‖ =
      ‖(D * Matrix.diagonal f -
        Matrix.diagonal f * D).toEuclideanLin.toContinuousLinearMap‖ := by
  rw [← fiveFibre_reindex_commutator]
  exact fiveFibre_reindex_operatorNorm e
    (D * Matrix.diagonal f - Matrix.diagonal f * D)

end Neoplatonic.LTR
