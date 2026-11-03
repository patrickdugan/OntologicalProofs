import Neoplatonic.LTR.ComplexValuedObservableHilbert

/-!
# Algebra laws of continuous complex-valued observable multiplication

The canonical complex-valued representation on the infinite
ℓ²(ℕ,ℂ²) Hilbert sum preserves the unit, zero, addition,
pointwise multiplication and complex scalar multiplication.
The star/adjoint law is handled in the companion module.
-/

namespace Neoplatonic.LTR

open scoped lp

theorem complexValuedObservableMatrix_zero :
    complexValuedObservableMatrix 0 0 =
      (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexValuedObservableMatrix]

theorem complexValuedObservableBlock_zero :
    complexValuedObservableBlock 0 0 =
      (0 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) := by
  change (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexValuedObservableMatrix 0 0) = 0
  rw [complexValuedObservableMatrix_zero, map_zero]

theorem complexValuedObservableMatrix_smul (c a b : ℂ) :
    complexValuedObservableMatrix (c * a) (c * b) =
      c • complexValuedObservableMatrix a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexValuedObservableMatrix, Matrix.smul_apply]

theorem complexValuedObservableBlock_smul (c a b : ℂ) :
    complexValuedObservableBlock (c * a) (c * b) =
      c • complexValuedObservableBlock a b := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) A)
    (complexValuedObservableMatrix_smul c a b)
  simpa [complexValuedObservableBlock, map_smul] using h

/-- Pointwise complex multiplication corresponds to composition on
the full infinite complex Hilbert space. -/
theorem compactComplexObservablePi_mul
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X)
    (a b : X → ℂ) (ha : Continuous a) (hb : Continuous b) :
    compactComplexObservablePi left right (fun x => a x * b x) (ha.mul hb) =
      (compactComplexObservablePi left right a ha).comp
        (compactComplexObservablePi left right b hb) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  have hblock := congrArg
    (fun T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
      T (ψ j))
    (complexValuedObservableBlock_mul
      (a (left j)) (a (right j)) (b (left j)) (b (right j)))
  calc
    (compactComplexObservablePi left right (fun x => a x * b x)
        (ha.mul hb) ψ) j =
      complexValuedObservableBlock
        (a (left j) * b (left j))
        (a (right j) * b (right j)) (ψ j) :=
      compactComplexObservablePi_apply
        left right (fun x => a x * b x) (ha.mul hb) ψ j
    _ = complexValuedObservableBlock (a (left j)) (a (right j))
        (complexValuedObservableBlock (b (left j)) (b (right j)) (ψ j)) := by
      simpa only [ContinuousLinearMap.comp_apply] using hblock.symm
    _ = (((compactComplexObservablePi left right a ha).comp
          (compactComplexObservablePi left right b hb)) ψ) j := by
      rw [ContinuousLinearMap.comp_apply,
        compactComplexObservablePi_apply, compactComplexObservablePi_apply]

theorem compactComplexObservablePi_add
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X)
    (a b : X → ℂ) (ha : Continuous a) (hb : Continuous b) :
    compactComplexObservablePi left right (fun x => a x + b x) (ha.add hb) =
      compactComplexObservablePi left right a ha +
        compactComplexObservablePi left right b hb := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  have hadd := congrArg
    (fun T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
      T (ψ j))
    (complexValuedObservableBlock_add
      (a (left j)) (a (right j)) (b (left j)) (b (right j)))
  calc
    (compactComplexObservablePi left right (fun x => a x + b x)
        (ha.add hb) ψ) j =
      complexValuedObservableBlock
        (a (left j) + b (left j))
        (a (right j) + b (right j)) (ψ j) :=
      compactComplexObservablePi_apply
        left right (fun x => a x + b x) (ha.add hb) ψ j
    _ = complexValuedObservableBlock (a (left j)) (a (right j)) (ψ j) +
        complexValuedObservableBlock (b (left j)) (b (right j)) (ψ j) := by
      simpa only [ContinuousLinearMap.add_apply] using hadd
    _ = ((compactComplexObservablePi left right a ha +
          compactComplexObservablePi left right b hb) ψ) j := by
      rw [ContinuousLinearMap.add_apply, lp.coeFn_add, Pi.add_apply,
        compactComplexObservablePi_apply, compactComplexObservablePi_apply]

theorem compactComplexObservablePi_one
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) :
    compactComplexObservablePi left right (fun _ => 1) continuous_const =
      ContinuousLinearMap.id ℂ ComplexDiracBlockHilbert := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  calc
    (compactComplexObservablePi left right (fun _ => 1)
        continuous_const ψ) j =
      complexValuedObservableBlock 1 1 (ψ j) :=
        compactComplexObservablePi_apply left right
          (fun _ => 1) continuous_const ψ j
    _ = ψ j := by rw [complexValuedObservableBlock_one]; rfl
    _ = ((ContinuousLinearMap.id ℂ ComplexDiracBlockHilbert) ψ) j := rfl

theorem compactComplexObservablePi_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) :
    compactComplexObservablePi left right (fun _ => 0) continuous_const =
      (0 : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [compactComplexObservablePi_apply, complexValuedObservableBlock_zero]
  simp only [ContinuousLinearMap.zero_apply]
  rfl

theorem compactComplexObservablePi_smul
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (c : ℂ)
    (a : X → ℂ) (ha : Continuous a) :
    compactComplexObservablePi left right
      (fun x => c * a x) (continuous_const.mul ha) =
      c • compactComplexObservablePi left right a ha := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [compactComplexObservablePi_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_smul, Pi.smul_apply, compactComplexObservablePi_apply]
  rw [complexValuedObservableBlock_smul]
  rfl

end Neoplatonic.LTR
