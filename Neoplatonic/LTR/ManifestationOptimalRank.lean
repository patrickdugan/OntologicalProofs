import Neoplatonic.LTR.ManifestationOptimalNorm
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# LTR-MAN-08C: exact dimension of the selected coordinate subspace

For every m-bit truth assignment we have a distinct marked Dirac block.
The first scalar coordinate of that block defines one standard Hilbert
basis vector in H = ℓ²(ℕ,ℂ²). Because selected block indices are
injective, these vectors form an orthonormal family.

The closed finite-dimensional span of these vectors has exactly 2^m
complex dimensions. This is the optimal finite-dimensional carrier
for the m-fragment; identifying it with the RANGE of the actual
rank-one-per-profile operator is the next theorem.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open scoped lp InnerProductSpace

/-- One standard Hilbert unit vector for each independent truth profile. -/
noncomputable def optimalManifestationBasisVector (m : ℕ)
    (bits : Fin m → Bool) : ComplexDiracBlockHilbert :=
  lp.single 2 (optimalManifestationBlock m bits)
    (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

/-- Exact orthonormality of the selected Hilbert coordinate family. -/
theorem optimalManifestationBasis_orthonormal (m : ℕ) :
    Orthonormal ℂ (optimalManifestationBasisVector m) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  change inner ℂ
      (lp.single 2 (optimalManifestationBlock m a)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)))
      (lp.single 2 (optimalManifestationBlock m b)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))) =
      if a = b then (1 : ℂ) else 0
  rw [lp.inner_single_left,
    EuclideanSpace.inner_single_left]
  simp only [map_one, one_mul]
  by_cases hab : a = b
  · subst b
    simp [lp.single_apply_self, EuclideanSpace.single]
  · have hneq :
        optimalManifestationBlock m a ≠
          optimalManifestationBlock m b := by
      intro heq
      exact hab ((optimalManifestationBlock_injective m) heq)
    rw [lp.single_apply_ne (p := (2 : ENNReal))
      (i := optimalManifestationBlock m b)
      (j := optimalManifestationBlock m a) hneq]
    simp [hab]

/-- Selected standard Hilbert vectors are linearly independent. -/
theorem optimalManifestationBasis_linearIndependent (m : ℕ) :
    LinearIndependent ℂ (optimalManifestationBasisVector m) :=
  (optimalManifestationBasis_orthonormal m).linearIndependent

/-- Their generated (finite-dimensional) complex subspace. -/
noncomputable def optimalManifestationCoordinateSpace (m : ℕ) :
    Submodule ℂ ComplexDiracBlockHilbert :=
  Submodule.span ℂ (Set.range (optimalManifestationBasisVector m))

/-- The selected coordinate space has rank exactly 2^m. -/
theorem optimalManifestationCoordinateSpace_finrank (m : ℕ) :
    Module.finrank ℂ (optimalManifestationCoordinateSpace m) = 2 ^ m := by
  classical
  have hd := (linearIndependent_iff_card_eq_finrank_span).mp
    (optimalManifestationBasis_linearIndependent m)
  change Module.finrank ℂ (Submodule.span ℂ
    (Set.range (optimalManifestationBasisVector m))) = 2 ^ m
  simpa [Fintype.card_fun] using hd.symm

end Neoplatonic.LTR.Nullary
