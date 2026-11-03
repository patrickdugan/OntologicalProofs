import Neoplatonic.LTR.ComplexOrdinaryResolventCompact

/-!
# A two-point complex observable representation and its exact Dirac commutator

For each marked pair, a real observable evaluates at its two endpoints.
The induced complex 2×2 diagonal matrix acts on the same Euclidean
Hilbert block as the genuine mass-shifted Dirac operator.

The block commutator is independent of the mass and has coefficient
scale * (b-a). This is the finite-dimensional algebraic input for a
uniformly bounded direct sum of commutator operators.
-/

namespace Neoplatonic.LTR

/-- Complex diagonal matrix representing a real observable's values at
the two ends of one marked edge. -/
def complexDiagonalObservable (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ), 0; 0, (b : ℂ)]

/-- Diagonal observable multiplication is pointwise. -/
theorem complexDiagonalObservable_mul
    (a b c d : ℝ) :
    complexDiagonalObservable a b * complexDiagonalObservable c d =
      complexDiagonalObservable (a * c) (b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiagonalObservable, Matrix.mul_apply, Fin.sum_univ_two] <;>
    push_cast <;> ring

/-- The constant observable acts as the identity matrix. -/
theorem complexDiagonalObservable_one :
    complexDiagonalObservable 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiagonalObservable, Matrix.one_apply]

/-- Each real-valued pairwise observable is Hermitian. -/
theorem complexDiagonalObservable_isHermitian (a b : ℝ) :
    (complexDiagonalObservable a b).IsHermitian := by
  change (complexDiagonalObservable a b).conjTranspose =
    complexDiagonalObservable a b
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiagonalObservable, Matrix.conjTranspose_apply]

/-- The mass term cancels from the exact complex matrix commutator. -/
theorem complexDirac_observable_commutator
    (mass scale a b : ℝ) :
    complexMassDirac mass scale * complexDiagonalObservable a b -
      complexDiagonalObservable a b * complexMassDirac mass scale =
      !![0, ((scale * (b - a) : ℝ) : ℂ);
        ((scale * (a - b) : ℝ) : ℂ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexMassDirac, complexDiagonalObservable,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    push_cast <;> ring

/-- The commutator is independent of the arbitrary diagonal mass. -/
theorem complexDirac_observable_commutator_mass_independent
    (mass otherMass scale a b : ℝ) :
    complexMassDirac mass scale * complexDiagonalObservable a b -
      complexDiagonalObservable a b * complexMassDirac mass scale =
    complexMassDirac otherMass scale * complexDiagonalObservable a b -
      complexDiagonalObservable a b * complexMassDirac otherMass scale := by
  rw [complexDirac_observable_commutator,
    complexDirac_observable_commutator]

/-- Genuine complex-linear Euclidean representation of two real values. -/
noncomputable def complexObservableBlock (a b : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexDiagonalObservable a b)

/-- Operator commutator equality on the actual two-point Euclidean space. -/
theorem complexObservableBlock_commutator
    (mass scale a b : ℝ) :
    (complexEuclideanDiracBlock mass scale).comp
      (complexObservableBlock a b) -
      (complexObservableBlock a b).comp
        (complexEuclideanDiracBlock mass scale) =
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
        (!![0, ((scale * (b - a) : ℝ) : ℂ);
          ((scale * (a - b) : ℝ) : ℂ), 0]) := by
  change (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexMassDirac mass scale * complexDiagonalObservable a b -
      complexDiagonalObservable a b * complexMassDirac mass scale) = _
  rw [complexDirac_observable_commutator]

end Neoplatonic.LTR
