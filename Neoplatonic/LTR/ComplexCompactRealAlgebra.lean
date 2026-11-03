import Neoplatonic.LTR.ComplexCompactRealRepresentation

/-!
# Additive laws for the compact real-observable representation

The canonical bounded complex-linear representation of real continuous
functions on compact X already preserves the unit and pointwise
multiplication. This file proves its additivity and the zero law,
completing the basic real-ring representation identities.

The spectral Hilbert space remains complex; the represented
functions in this file are real-valued.
-/

namespace Neoplatonic.LTR

/-- Adding two real diagonal observables adds their endpoint values. -/
theorem complexDiagonalObservable_add (a b c d : ℝ) :
    complexDiagonalObservable (a + c) (b + d) =
      complexDiagonalObservable a b + complexDiagonalObservable c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexDiagonalObservable] <;> push_cast <;> ring

/-- The finite complex Euclidean observable block is additive. -/
theorem complexObservableBlock_add (a b c d : ℝ) :
    complexObservableBlock (a + c) (b + d) =
      complexObservableBlock a b + complexObservableBlock c d := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) A)
    (complexDiagonalObservable_add a b c d)
  simpa [complexObservableBlock, map_add] using h

/-- Pointwise addition of real functions becomes operator addition
on the genuine infinite complex Hilbert space. -/
theorem compactRealObservablePi_add
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X)
    (a b : X → ℝ) (ha : Continuous a) (hb : Continuous b) :
    compactRealObservablePi left right (fun x => a x + b x) (ha.add hb) =
      compactRealObservablePi left right a ha +
        compactRealObservablePi left right b hb := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  have hadd := congrArg
    (fun T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
      T (ψ j))
    (complexObservableBlock_add
      (a (left j)) (a (right j)) (b (left j)) (b (right j)))
  calc
    (compactRealObservablePi left right (fun x => a x + b x)
        (ha.add hb) ψ) j =
      complexObservableBlock
        (a (left j) + b (left j))
        (a (right j) + b (right j)) (ψ j) :=
      compactRealObservablePi_apply
        left right (fun x => a x + b x) (ha.add hb) ψ j
    _ = complexObservableBlock (a (left j)) (a (right j)) (ψ j) +
        complexObservableBlock (b (left j)) (b (right j)) (ψ j) := by
      simpa only [ContinuousLinearMap.add_apply] using hadd
    _ = ((compactRealObservablePi left right a ha +
          compactRealObservablePi left right b hb) ψ) j := by
      rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
        compactRealObservablePi_apply, compactRealObservablePi_apply]

/-- The zero real observable is represented by the zero operator. -/
theorem compactRealObservablePi_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) :
    compactRealObservablePi left right (fun _ => 0) continuous_const =
      (0 : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [compactRealObservablePi_apply]
  have hz : complexObservableBlock 0 0 = 0 :=
    (complexObservableBlock_eq_zero_iff 0 0).mpr ⟨rfl, rfl⟩
  simp only [hz, ContinuousLinearMap.zero_apply]
  rfl

end Neoplatonic.LTR
