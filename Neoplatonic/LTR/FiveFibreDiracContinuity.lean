import Neoplatonic.LTR.FiveFibreAdjacentNorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# LTR-MAN-34: finite-dimensional continuity of the Connes commutator norm

The four truth-coordinate values form a finite-dimensional complex
normed vector space. Their lift to the faithful five-dimensional
Hilbert chart is complex-linear, as is commutation with the fixed
Dirac matrix D.

The resulting map into continuous Hilbert-space operators is
complex-linear and automatically continuous by finite-dimensionality.
Its operator norm is a continuous real-valued function. This supplies
the sole outstanding continuity hypothesis in the MAN-33 compactness
and attainment theorem.
-/

namespace Neoplatonic.LTR

/-- The faithful lift of truth functions preserves addition. -/
theorem fiveFibreSquareLift_add
    (f g : Fin 4 → ℂ) :
    fiveFibreSquareLift (f + g) =
      fiveFibreSquareLift f + fiveFibreSquareLift g := by
  funext i
  fin_cases i <;>
    simp [fiveFibreSquareLift, Pi.add_apply]

/-- The faithful truth-function lift is complex-linear. -/
theorem fiveFibreSquareLift_smul
    (c : ℂ) (f : Fin 4 → ℂ) :
    fiveFibreSquareLift (c • f) =
      fun i => c * fiveFibreSquareLift f i := by
  funext i
  fin_cases i <;>
    simp [fiveFibreSquareLift, Pi.smul_apply, smul_eq_mul]

/-- The continuous Hilbert-space Dirac commutator is additive
as a function of the represented observable. -/
theorem fiveFibreSquareDiracComm_add
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f g : Fin 5 → ℂ) :
    fiveFibreSquareDiracComm D (f + g) =
      fiveFibreSquareDiracComm D f +
        fiveFibreSquareDiracComm D g := by
  have hmat :
      D * Matrix.diagonal (f + g) -
        Matrix.diagonal (f + g) * D =
      (D * Matrix.diagonal f -
        Matrix.diagonal f * D) +
      (D * Matrix.diagonal g -
        Matrix.diagonal g * D) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.add_apply]
    ring
  unfold fiveFibreSquareDiracComm
  rw [hmat]
  ext v
  simp

/-- Linear map from the four truth-coordinate values into genuine
continuous Hilbert operators, encoding the represented commutator. -/
noncomputable def fiveFibreSquareDiracFourLinearMap
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (Fin 4 → ℂ) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5)) where
  toFun f := fiveFibreSquareDiracComm D (fiveFibreSquareLift f)
  map_add' := by
    intro f g
    change fiveFibreSquareDiracComm D (fiveFibreSquareLift (f + g)) =
      fiveFibreSquareDiracComm D (fiveFibreSquareLift f) +
        fiveFibreSquareDiracComm D (fiveFibreSquareLift g)
    rw [fiveFibreSquareLift_add, fiveFibreSquareDiracComm_add]
  map_smul' := by
    intro c f
    change fiveFibreSquareDiracComm D (fiveFibreSquareLift (c • f)) =
      c • fiveFibreSquareDiracComm D (fiveFibreSquareLift f)
    rw [fiveFibreSquareLift_smul]
    exact fiveFibreSquareDiracComm_smul
      D (fiveFibreSquareLift f) c

/-- The fixed Dirac commutator norm of four complex truth values
is continuous. The proof uses finite-dimensional continuity of
linear maps, with the target the genuine operator norm topology. -/
theorem fiveFibreSquareDiracFourNorm_continuous
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    Continuous (fun f : Fin 4 → ℂ =>
      ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f)‖) := by
  have hlinear : Continuous (fiveFibreSquareDiracFourLinearMap D) :=
    (fiveFibreSquareDiracFourLinearMap D).continuous_of_finiteDimensional
  exact continuous_norm.comp hlinear

end Neoplatonic.LTR
