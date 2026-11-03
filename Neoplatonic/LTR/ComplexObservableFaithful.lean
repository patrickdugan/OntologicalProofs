import Neoplatonic.LTR.ComplexObservableCommutator

/-!
# Faithfulness of the marked two-point observable representation

The diagonal Euclidean block recovers both real endpoint values.
If the bounded direct-sum Hilbert representation is zero, testing
vectors supported in any one block shows both marked endpoint values
vanish. Thus the representation is faithful to its explicit
point-evaluation data.

For a space X, density of the marked endpoints plus continuity of
a : X → ℝ is what further upgrades this data-level result to
faithfulness on continuous functions C(X).
-/

namespace Neoplatonic.LTR

open scoped lp

/-- A two-point observable matrix vanishes exactly when both
real endpoint values vanish. -/
theorem complexDiagonalObservable_eq_zero_iff (a b : ℝ) :
    complexDiagonalObservable a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
    simp [complexDiagonalObservable] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [complexDiagonalObservable]

/-- The continuous complex Hilbert block is faithful to both
endpoint evaluations. -/
theorem complexObservableBlock_eq_zero_iff (a b : ℝ) :
    complexObservableBlock a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    apply (complexDiagonalObservable_eq_zero_iff a b).mp
    apply (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).injective
    simpa [complexObservableBlock] using h
  · rintro ⟨rfl, rfl⟩
    change (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
      (complexDiagonalObservable 0 0) = 0
    have h : complexDiagonalObservable 0 0 =
        (0 : Matrix (Fin 2) (Fin 2) ℂ) :=
      (complexDiagonalObservable_eq_zero_iff 0 0).mpr ⟨rfl, rfl⟩
    rw [h, map_zero]

/-- If the actual bounded representation vanishes, every marked
pair of real endpoint observations vanishes. -/
theorem complexPairObservableCLM_eq_zero_values
    (left right : ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hBound : ∀ j, |left j| ≤ M ∧ |right j| ≤ M)
    (hzero :
      complexPairObservableCLM left right M hM hBound = 0) :
    ∀ j, left j = 0 ∧ right j = 0 := by
  intro j
  have hblock :
      complexObservableBlock (left j) (right j) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg
      (fun T : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert =>
        (T (lp.single 2 j v)) j) hzero
    simpa [complexPairObservableCLM_apply] using h
  exact (complexObservableBlock_eq_zero_iff (left j) (right j)).mp hblock

end Neoplatonic.LTR
