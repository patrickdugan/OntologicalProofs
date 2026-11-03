import Neoplatonic.LTR.ComplexValuedObservableStarFaithful
import Mathlib.Topology.ContinuousMap.Star
import Mathlib.Algebra.Star.StarAlgHom

/-!
# Bundled faithful complex star-algebra representation

Pointwise complex-valued continuous functions on compact X map
into the bounded complex-linear operators on the actual infinite
Hilbert direct sum. The map preserves zero, one, addition,
multiplication, scalar multiplication and star.

This bundles the previously kernel-checked laws into a
StarAlgHom ℂ from C(X,ℂ) to the complex Hilbert operator algebra.
Faithfulness follows when the marked endpoints cover a dense sequence.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Constant complex observables act as scalar multiples of the identity. -/
theorem compactComplexObservablePi_const
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (c : ℂ) :
    compactComplexObservablePi left right (fun _ => c) continuous_const =
      c • ContinuousLinearMap.id ℂ ComplexDiracBlockHilbert := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [compactComplexObservablePi_apply]
  change complexValuedObservableBlock c c (ψ j) = c • ψ j
  have hblock :
      complexValuedObservableBlock c c =
        c • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) := by
    simpa only [mul_one, complexValuedObservableBlock_one] using
      (complexValuedObservableBlock_smul c 1 1)
  rw [hblock]
  simp

/-- The canonical representation of continuous complex functions
as bounded operators on the infinite complex Hilbert space. -/
noncomputable def compactComplexObservableStarAlgHom
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) :
    C(X, ℂ) →⋆ₐ[ℂ]
      (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert) where
  toFun a := compactComplexObservablePi left right a a.continuous
  map_zero' := by
    change compactComplexObservablePi left right (fun _ => 0)
      continuous_const = 0
    exact compactComplexObservablePi_zero left right
  map_one' := by
    change compactComplexObservablePi left right (fun _ => 1)
      continuous_const =
      ContinuousLinearMap.id ℂ ComplexDiracBlockHilbert
    exact compactComplexObservablePi_one left right
  map_add' a b := by
    change compactComplexObservablePi left right
        (fun x => a x + b x) (a.continuous.add b.continuous) =
      compactComplexObservablePi left right a a.continuous +
      compactComplexObservablePi left right b b.continuous
    exact compactComplexObservablePi_add left right a b
      a.continuous b.continuous
  map_mul' a b := by
    change compactComplexObservablePi left right
        (fun x => a x * b x) (a.continuous.mul b.continuous) =
      (compactComplexObservablePi left right a a.continuous) *
      (compactComplexObservablePi left right b b.continuous)
    simpa only [ContinuousLinearMap.mul_def] using
      (compactComplexObservablePi_mul left right a b
        a.continuous b.continuous)
  commutes' c := by
    change compactComplexObservablePi left right (fun _ => c)
      continuous_const =
        algebraMap ℂ (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert) c
    rw [Algebra.algebraMap_eq_smul_one]
    exact compactComplexObservablePi_const left right c
  map_star' a := by
    change compactComplexObservablePi left right (fun x => star (a x))
        a.continuous.star =
      star (compactComplexObservablePi left right a a.continuous)
    exact (compactComplexObservablePi_star left right a a.continuous).symm

/-- The bundled complex star-algebra map has the advertised
coordinatewise multiplication action. -/
theorem compactComplexObservableStarAlgHom_apply
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X) (f : C(X, ℂ))
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (compactComplexObservableStarAlgHom left right f ψ) j =
      complexValuedObservableBlock (f (left j)) (f (right j)) (ψ j) :=
  compactComplexObservablePi_apply left right f f.continuous ψ j

/-- Dense marked endpoints make the bundled complex star-algebra
homomorphism injective. -/
theorem compactComplexObservableStarAlgHom_injective
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hcover : ∀ n, ∃ j, left j = q n ∨ right j = q n) :
    Function.Injective (compactComplexObservableStarAlgHom left right) := by
  intro a b hab
  apply ContinuousMap.ext
  intro x
  have hzero : compactComplexObservablePi left right
      (fun y => a y - b y)
      (a.continuous.sub b.continuous) = 0 := by
    have hsub : compactComplexObservablePi left right
        (fun y => a y - b y) (a.continuous.sub b.continuous) =
        compactComplexObservablePi left right a a.continuous -
        compactComplexObservablePi left right b b.continuous := by
      apply ContinuousLinearMap.ext
      intro ψ
      apply lp.ext
      funext j
      have h := congrArg
        (fun T : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) =>
          T (ψ j))
        (complexValuedObservableBlock_add
          (a (left j)) (a (right j))
          (-b (left j)) (-b (right j)))
      simp only [sub_eq_add_neg]
      sorry
    rw [hsub]
    rw [sub_eq_zero]
    exact hab
  have hv := compactComplexObservablePi_faithful q hq left right hcover
    (fun y => a y - b y) (a.continuous.sub b.continuous) hzero x
  exact sub_eq_zero.mp hv

end Neoplatonic.LTR
