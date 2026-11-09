import Neoplatonic.LTR.TwoDirectionExtremalEigenspaces
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# LTR-MAN-16: a nonzero two-edge path through a one-dimensional fibre

In the two-bit Dirac obstruction, let H_v be the one-dimensional
complex Hilbert fibre at a truth vertex v. If both distinct
one-proposition edge couplings meeting at v are nonzero, then
their ordered two-step product is nonzero.

The algebraic content is a universal fact about complex-linear
maps through the one-dimensional module ℂ:

  f : ℂ →ₗ[ℂ] U,  g : W →ₗ[ℂ] ℂ,
  f ≠ 0, g ≠ 0  ==>  f.comp g ≠ 0.

The proof uses the fact that a linear map from the scalar field is
determined by its value at 1, and that multiplication by a nonzero
scalar cannot annihilate a nonzero vector.

This is a necessary bridge from AB=0 to the degree-at-most-one
restriction on one-dimensional vertex fibres. Transporting it along
a chosen equivalence H_v ≃ₗ[ℂ] ℂ and identifying the exact blocks
of the coordinate commutator product remain separate obligations.
-/

namespace Neoplatonic.LTR

/-- Every complex-linear map from ℂ is determined by its value at 1. -/
theorem complexLine_linearMap_apply_one
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    (f : ℂ →ₗ[ℂ] U) (z : ℂ) :
    f z = z • f 1 := by
  simpa only [smul_eq_mul, mul_one] using (f.map_smul z (1 : ℂ))

/-- If a complex-linear map from the scalar line is nonzero,
its value on the unit scalar is nonzero. -/
theorem complexLine_linearMap_one_ne_zero
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    (f : ℂ →ₗ[ℂ] U) (hf : f ≠ 0) :
    f 1 ≠ 0 := by
  intro hzero
  apply hf
  apply LinearMap.ext
  intro z
  rw [complexLine_linearMap_apply_one f z, hzero, smul_zero]
  rfl

/-- Two nonzero complex-linear maps cannot have zero composition
when their intermediate space is one-dimensional. -/
theorem complexLine_nonzero_maps_comp_ne_zero
    {U W : Type*}
    [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W]
    (f : ℂ →ₗ[ℂ] U) (g : W →ₗ[ℂ] ℂ)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    f.comp g ≠ 0 := by
  have hf1 : f 1 ≠ 0 := complexLine_linearMap_one_ne_zero f hf
  have hex : ∃ w : W, g w ≠ 0 := by
    have hn : ¬ ∀ w : W, g w = 0 := by
      intro hz
      apply hg
      apply LinearMap.ext
      intro w
      exact hz w
    exact not_forall.mp hn
  obtain ⟨w, hgw⟩ := hex
  intro hcomp
  have hzero : f (g w) = 0 := by
    have h := congrArg (fun t : W →ₗ[ℂ] U => t w) hcomp
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have hnonzero : f (g w) ≠ 0 := by
    rw [complexLine_linearMap_apply_one]
    exact smul_ne_zero hgw hf1
  exact hnonzero hzero

end Neoplatonic.LTR
