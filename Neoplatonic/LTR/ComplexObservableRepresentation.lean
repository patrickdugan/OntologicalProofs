import Neoplatonic.LTR.ComplexObservableNorm

/-!
# Bounded complex Hilbert representation of real two-point observables

For uniformly bounded real value sequences left_j and right_j, the
two-point diagonal matrices determine a continuous complex-linear
operator π(left,right) on ℓ²(ℕ,ℂ²). It is an actual Hilbert-space
representation of the observable data, with a checked norm bound.

An effective logical marking and density of the chosen endpoints in a
Stone completion space are additional structures, developed separately.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Complex two-point observable is the ordinary diagonal matrix. -/
theorem complexDiagonalObservable_eq_diagonal (a b : ℝ) :
    complexDiagonalObservable a b =
      Matrix.diagonal (fun i : Fin 2 =>
        if i = 0 then (a : ℂ) else (b : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiagonalObservable, Matrix.diagonal_apply]

/-- Real pairwise observable values bounded by M give a complex block
operator of norm at most M. -/
theorem complexObservableBlock_norm_le
    (a b M : ℝ) (hM : 0 ≤ M)
    (ha : |a| ≤ M) (hb : |b| ≤ M) :
    ‖complexObservableBlock a b‖ ≤ M := by
  change ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexDiagonalObservable a b)‖ ≤ M
  rw [Matrix.l2_opNorm_toEuclideanCLM,
    complexDiagonalObservable_eq_diagonal,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

/-- The pairwise observable block respects pointwise multiplication. -/
theorem complexObservableBlock_mul
    (a b c d : ℝ) :
    (complexObservableBlock a b).comp
      (complexObservableBlock c d) =
        complexObservableBlock (a*c) (b*d) := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) A)
    (complexDiagonalObservable_mul a b c d)
  change ((Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
      (complexDiagonalObservable a b)).comp
    ((Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
      (complexDiagonalObservable c d)) =
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
      (complexDiagonalObservable (a*c) (b*d))
  rw [← ContinuousLinearMap.mul_def]
  simpa only [map_mul] using h

/-- The pairwise constant-one observable is the identity endomorphism. -/
theorem complexObservableBlock_one :
    complexObservableBlock 1 1 =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) := by
  change (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexDiagonalObservable 1 1) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2))
  rw [complexDiagonalObservable_one]
  exact map_one _

/-- A bounded pairwise real observable on the infinite Hilbert space. -/
noncomputable def complexPairObservableCLM
    (left right : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ j, |left j| ≤ M ∧ |right j| ≤ M) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  lp.mapCLM 2
    (fun j => complexObservableBlock (left j) (right j))
    hM
    (fun j => complexObservableBlock_norm_le
      (left j) (right j) M hM (hbound j).1 (hbound j).2)

/-- The global representation acts at each Hilbert block by the
corresponding diagonal complex matrix. -/
theorem complexPairObservableCLM_apply
    (left right : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ j, |left j| ≤ M ∧ |right j| ≤ M)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (complexPairObservableCLM left right M hM hbound ψ) j =
       complexObservableBlock (left j) (right j) (ψ j) := by
  change complexObservableBlock (left j) (right j) (ψ j) = _
  rfl

/-- The Hilbert representation has the same uniform operator bound. -/
theorem complexPairObservableCLM_norm_le
    (left right : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hbound : ∀ j, |left j| ≤ M ∧ |right j| ≤ M) :
    ‖complexPairObservableCLM left right M hM hbound‖ ≤ M :=
  lp.norm_mapCLM_le 2
    (fun j => complexObservableBlock (left j) (right j))
    hM
    (fun j => complexObservableBlock_norm_le
      (left j) (right j) M hM (hbound j).1 (hbound j).2)

end Neoplatonic.LTR
