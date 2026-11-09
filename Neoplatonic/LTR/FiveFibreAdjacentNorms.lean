import Neoplatonic.LTR.FiveFibreOppositeContractions
import Mathlib.Tactic

/-!
# LTR-MAN-29: adjacent Hamming dual bounds force unit coordinate norms

The Connes dual upper bounds on the unit edges 00--01 and 00--10
force the corresponding coordinate commutator norms to be at least
one. The proof rescales each coordinate observable, using the exact
homogeneity of the finite-matrix Dirac commutator and the genuine
continuous complex Hilbert-space operator norm.

Admissibility of the two opposite-corner witnesses supplies the
reverse operator bounds through MAN-28. Thus both coordinate
commutators have norm exactly one, as required by the graded
five-dimensional spectral zero-product theorem MAN-21.

The dual upper bounds and the admissibility of the opposite
witnesses are given explicitly as hypotheses. The next bridge is
their derivation from the six exact Connes distances.
-/

namespace Neoplatonic.LTR

/-- The actual continuous Hilbert-space commutator for a
diagonal five-coordinate observable. -/
noncomputable def fiveFibreSquareDiracComm
    (D : Matrix (Fin 5) (Fin 5) ℂ) (f : Fin 5 → ℂ) :
    EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5) :=
  (D * Matrix.diagonal f - Matrix.diagonal f * D
    ).toEuclideanLin.toContinuousLinearMap

/-- Scalar homogeneity of the represented Dirac commutator. -/
theorem fiveFibreSquareDiracComm_smul
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Fin 5 → ℂ) (t : ℂ) :
    fiveFibreSquareDiracComm D (fun i => t * f i) =
      t • fiveFibreSquareDiracComm D f := by
  have hmatrix :
      D * Matrix.diagonal (fun i => t * f i) -
        Matrix.diagonal (fun i => t * f i) * D =
      t • (D * Matrix.diagonal f - Matrix.diagonal f * D) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    ring
  unfold fiveFibreSquareDiracComm
  rw [hmatrix]
  ext v
  simp

/-- A complex-linear vector with a dual unit-ball functional
detecting every scalar multiple must have norm at least one. -/
theorem complexUnitBallDual_norm_ge_one
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (x : X)
    (hdual : ∀ t : ℂ, ‖t • x‖ ≤ 1 → ‖t‖ ≤ 1) :
    1 ≤ ‖x‖ := by
  by_contra hn
  have hlt : ‖x‖ < 1 := lt_of_not_ge hn
  by_cases hx : x = 0
  · subst x
    have hbad := hdual (2 : ℂ) (by simp)
    norm_num at hbad
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let t : ℂ := ((‖x‖⁻¹ : ℝ) : ℂ)
    have ht : ‖t‖ = ‖x‖⁻¹ := by
      simp [t, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    have hunit : ‖t • x‖ ≤ 1 := by
      rw [norm_smul, ht]
      simpa using (le_of_eq (inv_mul_cancel₀ hpos.ne'))
    have hle : ‖x‖⁻¹ ≤ 1 := by
      simpa only [ht] using hdual t hunit
    exact (not_lt_of_ge hle) ((one_lt_inv₀ hpos).mpr hlt)

/-- The 00--01 Connes dual edge upper bound forces the first
Hermitian coordinate commutator's genuine operator norm to be ≥1. -/
theorem fiveFibreSquare_firstCoordinate_norm_ge_one
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hdual : ∀ f : Fin 5 → ℂ, f 4 = f 0 →
      ‖fiveFibreSquareDiracComm D f‖ ≤ 1 →
      ‖f 0 - f 1‖ ≤ 1) :
    1 ≤ ‖(fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap‖ := by
  have hnorm :
      ‖(fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap‖ =
        ‖fiveFibreSquareDiracComm D fiveFibreSquareP‖ := by
    unfold fiveFibreSquareDiracComm
    rw [fiveFibreSquareA_eq_diagonal_commutator,
      fiveFibreSquare_imaginaryOperator_norm]
  apply complexUnitBallDual_norm_ge_one
  intro t ht
  let f : Fin 5 → ℂ := fun i => t * fiveFibreSquareP i
  have hf : f 4 = f 0 := by norm_num [f, fiveFibreSquareP]
  have hscale :
      ‖fiveFibreSquareDiracComm D f‖ =
        ‖t • (fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap‖ := by
    calc
      ‖fiveFibreSquareDiracComm D f‖ =
          ‖t • fiveFibreSquareDiracComm D fiveFibreSquareP‖ := by
        change ‖fiveFibreSquareDiracComm D
          (fun i => t * fiveFibreSquareP i)‖ = _
        rw [fiveFibreSquareDiracComm_smul]
      _ = ‖t • (fiveFibreSquareA D
          ).toEuclideanLin.toContinuousLinearMap‖ := by
        simp only [norm_smul, ← hnorm]
  have hunit : ‖fiveFibreSquareDiracComm D f‖ ≤ 1 := by
    rw [hscale]
    exact ht
  have hv := hdual f hf hunit
  simpa [f, fiveFibreSquareP] using hv

/-- The 00--10 Connes dual edge upper bound forces the second
Hermitian coordinate commutator's genuine operator norm to be ≥1. -/
theorem fiveFibreSquare_secondCoordinate_norm_ge_one
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hdual : ∀ f : Fin 5 → ℂ, f 4 = f 0 →
      ‖fiveFibreSquareDiracComm D f‖ ≤ 1 →
      ‖f 0 - f 2‖ ≤ 1) :
    1 ≤ ‖(fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap‖ := by
  have hnorm :
      ‖(fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap‖ =
        ‖fiveFibreSquareDiracComm D fiveFibreSquareQ‖ := by
    unfold fiveFibreSquareDiracComm
    rw [fiveFibreSquareB_eq_diagonal_commutator,
      fiveFibreSquare_imaginaryOperator_norm]
  apply complexUnitBallDual_norm_ge_one
  intro t ht
  let f : Fin 5 → ℂ := fun i => t * fiveFibreSquareQ i
  have hf : f 4 = f 0 := by norm_num [f, fiveFibreSquareQ]
  have hscale :
      ‖fiveFibreSquareDiracComm D f‖ =
        ‖t • (fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap‖ := by
    calc
      ‖fiveFibreSquareDiracComm D f‖ =
          ‖t • fiveFibreSquareDiracComm D fiveFibreSquareQ‖ := by
        change ‖fiveFibreSquareDiracComm D
          (fun i => t * fiveFibreSquareQ i)‖ = _
        rw [fiveFibreSquareDiracComm_smul]
      _ = ‖t • (fiveFibreSquareB D
          ).toEuclideanLin.toContinuousLinearMap‖ := by
        simp only [norm_smul, ← hnorm]
  have hunit : ‖fiveFibreSquareDiracComm D f‖ ≤ 1 := by
    rw [hscale]
    exact ht
  have hv := hdual f hf hunit
  simpa [f, fiveFibreSquareQ] using hv

/-- If both the sum and difference of two normed complex-space
vectors have norm ≤1, each individual vector has norm ≤1. -/
theorem twoDirection_norms_le_one
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (a b : X) (hplus : ‖a + b‖ ≤ 1) (hminus : ‖a - b‖ ≤ 1) :
    ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 := by
  have haeq : (a + b) + (a - b) = (2 : ℂ) • a := by
    module
  have hbeq : (a + b) - (a - b) = (2 : ℂ) • b := by
    module
  have ha : ‖(2 : ℂ) • a‖ ≤ (2 : ℝ) := by
    rw [← haeq]
    calc
      ‖(a + b) + (a - b)‖ ≤ ‖a + b‖ + ‖a - b‖ :=
        norm_add_le _ _
      _ ≤ 2 := by linarith
  have hb : ‖(2 : ℂ) • b‖ ≤ (2 : ℝ) := by
    rw [← hbeq]
    calc
      ‖(a + b) - (a - b)‖ ≤ ‖a + b‖ + ‖a - b‖ :=
        norm_sub_le _ _
      _ ≤ 2 := by linarith
  constructor
  · rw [norm_smul] at ha
    norm_num at ha
    linarith
  · rw [norm_smul] at hb
    norm_num at hb
    linarith

/-- Exact adjacent dual upper bounds, together with admissibility of
the two opposite-corner witnesses, force both coordinate commutators
to have norm exactly one. -/
theorem fiveFibreSquare_adjacentDual_normOne
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (h01 : ∀ f : Fin 5 → ℂ, f 4 = f 0 →
      ‖fiveFibreSquareDiracComm D f‖ ≤ 1 →
      ‖f 0 - f 1‖ ≤ 1)
    (h02 : ∀ f : Fin 5 → ℂ, f 4 = f 0 →
      ‖fiveFibreSquareDiracComm D f‖ ≤ 1 →
      ‖f 0 - f 2‖ ≤ 1)
    (hsum :
      ‖fiveFibreSquareDiracComm D
        (fiveFibreSquareLift twoBitOppositeCornerSum)‖ ≤ 1)
    (hdiff :
      ‖fiveFibreSquareDiracComm D
        (fiveFibreSquareLift twoBitOppositeCornerDifference)‖ ≤ 1) :
    ‖(fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap‖ = 1 ∧
    ‖(fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap‖ = 1 := by
  let a : EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5) :=
    (fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap
  let b : EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5) :=
    (fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap
  have hab := fiveFibreSquare_oppositeWitnesses_contractions
    D (by simpa only [fiveFibreSquareDiracComm] using hsum)
      (by simpa only [fiveFibreSquareDiracComm] using hdiff)
  have hplus : ‖a + b‖ ≤ 1 := by
    have h : (fiveFibreSquareA D + fiveFibreSquareB D
      ).toEuclideanLin.toContinuousLinearMap = a + b := by
      ext v
      simp [a, b]
    rw [← h]
    exact hab.1
  have hminus : ‖a - b‖ ≤ 1 := by
    have h : (fiveFibreSquareA D - fiveFibreSquareB D
      ).toEuclideanLin.toContinuousLinearMap = a - b := by
      ext v
      simp [a, b]
    rw [← h]
    exact hab.2
  obtain ⟨hale, hble⟩ := twoDirection_norms_le_one a b hplus hminus
  have hage : 1 ≤ ‖a‖ :=
    fiveFibreSquare_firstCoordinate_norm_ge_one D h01
  have hbge : 1 ≤ ‖b‖ :=
    fiveFibreSquare_secondCoordinate_norm_ge_one D h02
  exact ⟨le_antisymm hale hage, le_antisymm hble hbge⟩

end Neoplatonic.LTR
