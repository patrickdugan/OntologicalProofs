import Neoplatonic.LTR.SixDimensionalAmbientSignedInvolution
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# LTR-MAN-144: exact Hilbert signed-square defect is the residual projection

Suppose the square of a bounded complex Hilbert operator T fixes a
finite quartet q pointwise and acts as multiplication by a scalar
mu on the orthogonal complement of the quartet's span.

The entire operator defect then equals
  I - T² = (1 - mu) • P_res
where P_res is the genuine orthogonal Hilbert projection onto
(span(q))ᗮ. This is an operator identity on the original ambient
space, independent of any chosen eigenbasis in the residual.

If the residual submodule is nonzero, the norm of its orthogonal
projection is one, giving the exact C*-norm identity
  ||I-T²|| = |1-mu|.

These abstract lemmas are used with the signed Hamming quartet and
its two-dimensional residual, and eventually with the genuine
complex 6x6 Dirac coordinate matrices.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

/-- A square fixing each spanning quartet vector and acting by a
scalar on the orthogonal complement differs from identity by that
scalar times the orthogonal projection onto the complement. -/
theorem hilbert_square_defect_eq_residual_projection
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (q : Fin 4 → E) (mu : ℂ)
    (hquartet : ∀ i : Fin 4, T (T (q i)) = q i)
    (hresidual : ∀ x ∈ (Submodule.span ℂ (Set.range q))ᗮ,
      T (T x) = mu • x) :
    (1 : E →L[ℂ] E) - T * T =
      ((1 : ℂ) - mu) •
        ((Submodule.span ℂ (Set.range q))ᗮ).starProjection := by
  let K : Submodule ℂ E := Submodule.span ℂ (Set.range q)
  have hK : ∀ x ∈ K, T (T x) = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hquartet i
    | zero => simp
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using congrArg₂ (· + ·) ihx ihy
    | smul a x hx ihx =>
        simpa only [map_smul] using
          congrArg (fun y : E => a • y) ihx
  have hsup : K ⊔ Kᗮ = ⊤ :=
    (K.isCompl_orthogonal).sup_eq_top
  apply ContinuousLinearMap.ext
  intro x
  have hx : x ∈ K ⊔ Kᗮ := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.mp hx
  have hsum' : y + z = x := by simpa only using hsum
  have hPy : Kᗮ.starProjection y = 0 :=
    K.starProjection_orthogonal_apply_eq_zero hy
  have hPz : Kᗮ.starProjection z = z :=
    Kᗮ.starProjection_eq_self_iff.mpr hz
  change x - T (T x) =
    (((1 : ℂ) - mu) • Kᗮ.starProjection) x
  rw [← hsum']
  simp only [map_add, hK y hy, hresidual z hz,
    ContinuousLinearMap.smul_apply, hPy, hPz]
  module

/-- If the residual space has positive dimension, the full
spectral defect has exactly the absolute scalar residual defect
as its Hilbert C*-operator norm. -/
theorem hilbert_square_defect_norm_eq_residual_scalar
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (q : Fin 4 → E) (mu : ℂ)
    (hquartet : ∀ i : Fin 4, T (T (q i)) = q i)
    (hresidual : ∀ x ∈ (Submodule.span ℂ (Set.range q))ᗮ,
      T (T x) = mu • x)
    (hNonzero : (Submodule.span ℂ (Set.range q))ᗮ ≠ ⊥) :
    ‖(1 : E →L[ℂ] E) - T * T‖ = ‖(1 : ℂ) - mu‖ := by
  rw [hilbert_square_defect_eq_residual_projection
    T q mu hquartet hresidual]
  rw [norm_smul,
    (Submodule.span ℂ (Set.range q))ᗮ.norm_starProjection hNonzero]
  simp

end Neoplatonic.LTR
