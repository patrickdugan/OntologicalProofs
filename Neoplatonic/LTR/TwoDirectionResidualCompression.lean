import Neoplatonic.LTR.TwoDirectionResidualSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# LTR-MAN-60: the actual compressed residual Hilbert operators

MAN-58 constructs the signed extremal quartet and MAN-59 proves the
orthogonal complement of its span is invariant under both coordinate
commutators. This module restricts each ambient continuous linear
operator to that genuine residual Hilbert submodule.

The restricted operators preserve their Hilbert inner-product
symmetry and inherit the two simultaneous sum/difference operator
contractions. Their pointwise Pythagorean bound, individual norm
bounds, and ordered products are identities of bounded Hilbert
operators, so the remaining 6D/7D search can work directly with
Hermitian operators on residual dimensions two and three.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- An invariant submodule inherits an operator whose genuine
Hilbert operator norm is bounded by the ambient norm. -/
theorem invariantHilbertRestriction_norm_le
    (T : E →L[ℂ] E) (R : Submodule ℂ E)
    (hR : ∀ x ∈ R, T x ∈ R) :
    ‖T.restrict hR‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro x
  change ‖T (x : E)‖ ≤ ‖T‖ * ‖(x : E)‖
  exact T.le_opNorm (x : E)

/-- Two signed coordinate operators together with the four
extremal eigenvectors and simultaneous contraction hypotheses. -/
structure TwoDirectionExtremalSystem (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] where
  A : E →L[ℂ] E
  B : E →L[ℂ] E
  uplus : E
  uminus : E
  vplus : E
  vminus : E
  plus_le : ‖A + B‖ ≤ 1
  minus_le : ‖A - B‖ ≤ 1
  A_self : IsSelfAdjoint A
  B_self : IsSelfAdjoint B
  A_uplus : A uplus = uplus
  A_uminus : A uminus = -uminus
  B_vplus : B vplus = vplus
  B_vminus : B vminus = -vminus

namespace TwoDirectionExtremalSystem

/-- The invariant orthogonal residual Hilbert submodule. -/
noncomputable def residual (S : TwoDirectionExtremalSystem E) : Submodule ℂ E :=
  twoDirectionResidualSubmodule S.uplus S.uminus S.vplus S.vminus

/-- MAN-59 gives invariance under both original coordinate
operators for every element of the residual submodule. -/
theorem residual_invariant (S : TwoDirectionExtremalSystem E)
    (x : E) (hx : x ∈ S.residual) :
    S.A x ∈ S.residual ∧ S.B x ∈ S.residual :=
  twoDirection_residualSubmodule_invariant
    S.A S.B S.plus_le S.minus_le S.A_self S.B_self
    S.uplus S.uminus S.vplus S.vminus
    S.A_uplus S.A_uminus S.B_vplus S.B_vminus x hx

/-- Compression of A to the genuine residual subspace. -/
noncomputable def residualA (S : TwoDirectionExtremalSystem E) :
    S.residual →L[ℂ] S.residual :=
  S.A.restrict (fun x hx => (S.residual_invariant x hx).1)

/-- Compression of B to the same residual subspace. -/
noncomputable def residualB (S : TwoDirectionExtremalSystem E) :
    S.residual →L[ℂ] S.residual :=
  S.B.restrict (fun x hx => (S.residual_invariant x hx).2)

@[simp]
theorem residualA_apply_coe (S : TwoDirectionExtremalSystem E)
    (x : S.residual) :
    ((S.residualA x : S.residual) : E) = S.A (x : E) := rfl

@[simp]
theorem residualB_apply_coe (S : TwoDirectionExtremalSystem E)
    (x : S.residual) :
    ((S.residualB x : S.residual) : E) = S.B (x : E) := rfl

/-- Compression preserves the self-adjoint symmetry of A on
the true residual complex Hilbert inner product. -/
theorem residualA_symmetric (S : TwoDirectionExtremalSystem E) :
    S.residualA.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ (S.A (x : E)) (y : E) =
    inner ℂ (x : E) (S.A (y : E))
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp S.A_self)
    (x : E) (y : E)

/-- Compression preserves the self-adjoint symmetry of B. -/
theorem residualB_symmetric (S : TwoDirectionExtremalSystem E) :
    S.residualB.toLinearMap.IsSymmetric := by
  intro x y
  change inner ℂ (S.B (x : E)) (y : E) =
    inner ℂ (x : E) (S.B (y : E))
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp S.B_self)
    (x : E) (y : E)

/-- On the residual Hilbert space, the two compressed
coordinate operators remain simultaneous plus contractions. -/
theorem residual_plus_le (S : TwoDirectionExtremalSystem E) :
    ‖S.residualA + S.residualB‖ ≤ 1 := by
  have hmap : ∀ x ∈ S.residual, (S.A + S.B) x ∈ S.residual := by
    intro x hx
    obtain ⟨ha, hb⟩ := S.residual_invariant x hx
    change S.A x + S.B x ∈ S.residual
    exact S.residual.add_mem ha hb
  have heq : S.residualA + S.residualB =
      (S.A + S.B).restrict hmap := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  rw [heq]
  exact (invariantHilbertRestriction_norm_le (S.A + S.B)
    S.residual hmap).trans S.plus_le

/-- The compressed difference is a contraction as well. -/
theorem residual_minus_le (S : TwoDirectionExtremalSystem E) :
    ‖S.residualA - S.residualB‖ ≤ 1 := by
  have hmap : ∀ x ∈ S.residual, (S.A - S.B) x ∈ S.residual := by
    intro x hx
    obtain ⟨ha, hb⟩ := S.residual_invariant x hx
    change S.A x - S.B x ∈ S.residual
    exact S.residual.sub_mem ha hb
  have heq : S.residualA - S.residualB =
      (S.A - S.B).restrict hmap := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  rw [heq]
  exact (invariantHilbertRestriction_norm_le (S.A - S.B)
    S.residual hmap).trans S.minus_le

/-- Pythagorean contraction survives compression to the residual
Hilbert sector, including dimensions two and three. -/
theorem residual_pythagorean (S : TwoDirectionExtremalSystem E)
    (x : S.residual) :
    ‖S.residualA x‖ ^ 2 + ‖S.residualB x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  twoDirection_parallelogram_contraction
    S.residualA S.residualB
    S.residual_plus_le S.residual_minus_le x

/-- Each individual compressed coordinate operator is a
contraction of the genuine residual Hilbert norm. -/
theorem residualA_norm_le_one (S : TwoDirectionExtremalSystem E) :
    ‖S.residualA‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  have hp := S.residual_pythagorean x
  have hsq : ‖S.residualA x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖S.residualB x‖)]
  have hx := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hsq
  simpa only [one_mul] using hx

theorem residualB_norm_le_one (S : TwoDirectionExtremalSystem E) :
    ‖S.residualB‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  have hp := S.residual_pythagorean x
  have hsq : ‖S.residualB x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖S.residualA x‖)]
  have hx := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hsq
  simpa only [one_mul] using hx

/-- The ordered operator products on the residual space are
the restrictions of the ambient ordered products. -/
theorem residualAB_apply_coe (S : TwoDirectionExtremalSystem E)
    (x : S.residual) :
    (((S.residualA.comp S.residualB) x : S.residual) : E) =
      S.A (S.B (x : E)) := rfl

theorem residualBA_apply_coe (S : TwoDirectionExtremalSystem E)
    (x : S.residual) :
    (((S.residualB.comp S.residualA) x : S.residual) : E) =
      S.B (S.A (x : E)) := rfl

end TwoDirectionExtremalSystem
end Neoplatonic.LTR
