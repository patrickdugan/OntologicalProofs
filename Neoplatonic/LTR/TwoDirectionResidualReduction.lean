import Neoplatonic.LTR.FiveDimensionalGradedZeroProduct
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic

/-!
# LTR-MAN-56: two-direction residual eigenspace decomposition

The opposite-corner Connes witnesses produce contractions A+B and A-B
and signed unit eigenvectors u+,u- of A and v+,v- of B. The
parallelogram argument forces B to annihilate u+,u- and A to
annihilate v+,v-.

Self-adjointness then preserves the orthogonal complement of all four
extremal vectors. Both products AB and BA annihilate the extremal
quartet. The remaining operator-product obstruction is concentrated
in a residual Hilbert space of dimension n - 4.

Mathlib's orthonormal-span finrank theorem certifies residual
dimensions two and three when the ambient dimension is six or seven.
This module does not assume that the residual commutator products
vanish: that claim is precisely what must be studied next.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A self-adjoint operator preserves orthogonality to each of its
eigenvectors, at an arbitrary complex eigenvalue. -/
theorem selfAdjoint_preserves_orthogonal_to_eigenvector
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (u x : E) (μ : ℂ)
    (hu : T u = μ • u)
    (hux : inner ℂ u x = 0) :
    inner ℂ u (T x) = 0 := by
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) u x
  change inner ℂ (T u) x = inner ℂ u (T x) at hs
  rw [hu] at hs
  have hz : inner ℂ (μ • u) x = 0 := by
    rw [inner_smul_left, hux]
    simp
  exact hs.symm.trans hz

/-- Orthogonality to the four extremal eigenvectors of the two
coordinate operators. -/
def twoDirectionExtremalResidual
    (uplus uminus vplus vminus x : E) : Prop :=
  inner ℂ uplus x = 0 ∧
  inner ℂ uminus x = 0 ∧
  inner ℂ vplus x = 0 ∧
  inner ℂ vminus x = 0

/-- The residual complement is invariant under each coordinate
operator. The Hamming contraction hypotheses force cross-annihilation,
and the self-adjoint operators preserve the four orthogonality equations. -/
theorem twoDirection_extremalResidual_invariant
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (hAself : IsSelfAdjoint A)
    (hBself : IsSelfAdjoint B)
    (uplus uminus vplus vminus x : E)
    (hAuplus : A uplus = uplus)
    (hAuminus : A uminus = -uminus)
    (hBvplus : B vplus = vplus)
    (hBvminus : B vminus = -vminus)
    (hx : twoDirectionExtremalResidual uplus uminus vplus vminus x) :
    twoDirectionExtremalResidual uplus uminus vplus vminus (A x) ∧
    twoDirectionExtremalResidual uplus uminus vplus vminus (B x) := by
  obtain ⟨huxp, huxm, hvxp, hvxm⟩ := hx
  have hBuplus : B uplus = 0 :=
    twoDirection_unitEigenvector_annihilates_second A B
      hplus hminus 1 (by norm_num) uplus (by simpa using hAuplus)
  have hBuminus : B uminus = 0 :=
    twoDirection_unitEigenvector_annihilates_second A B
      hplus hminus (-1) (by norm_num) uminus (by simpa using hAuminus)
  have hAvplus : A vplus = 0 :=
    twoDirection_unitEigenvector_annihilates_first A B
      hplus hminus 1 (by norm_num) vplus (by simpa using hBvplus)
  have hAvminus : A vminus = 0 :=
    twoDirection_unitEigenvector_annihilates_first A B
      hplus hminus (-1) (by norm_num) vminus (by simpa using hBvminus)
  constructor
  · exact ⟨
      selfAdjoint_preserves_orthogonal_to_eigenvector A hAself
        uplus x 1 (by simpa using hAuplus) huxp,
      selfAdjoint_preserves_orthogonal_to_eigenvector A hAself
        uminus x (-1) (by simpa using hAuminus) huxm,
      selfAdjoint_preserves_orthogonal_to_eigenvector A hAself
        vplus x 0 (by simp [hAvplus]) hvxp,
      selfAdjoint_preserves_orthogonal_to_eigenvector A hAself
        vminus x 0 (by simp [hAvminus]) hvxm⟩
  · exact ⟨
      selfAdjoint_preserves_orthogonal_to_eigenvector B hBself
        uplus x 0 (by simp [hBuplus]) huxp,
      selfAdjoint_preserves_orthogonal_to_eigenvector B hBself
        uminus x 0 (by simp [hBuminus]) huxm,
      selfAdjoint_preserves_orthogonal_to_eigenvector B hBself
        vplus x 1 (by simpa using hBvplus) hvxp,
      selfAdjoint_preserves_orthogonal_to_eigenvector B hBself
        vminus x (-1) (by simpa using hBvminus) hvxm⟩

/-- Both ordered operator products vanish on the four signed
extremal vectors; all possible nonzero product action is residual. -/
theorem twoDirection_extremalProducts_vanish_on_quartet
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (uplus uminus vplus vminus : E)
    (hAuplus : A uplus = uplus)
    (hAuminus : A uminus = -uminus)
    (hBvplus : B vplus = vplus)
    (hBvminus : B vminus = -vminus) :
    (∀ u : E, u = uplus ∨ u = uminus ∨ u = vplus ∨ u = vminus →
      A (B u) = 0 ∧ B (A u) = 0) := by
  have hBuplus : B uplus = 0 :=
    twoDirection_unitEigenvector_annihilates_second A B
      hplus hminus 1 (by norm_num) uplus (by simpa using hAuplus)
  have hBuminus : B uminus = 0 :=
    twoDirection_unitEigenvector_annihilates_second A B
      hplus hminus (-1) (by norm_num) uminus (by simpa using hAuminus)
  have hAvplus : A vplus = 0 :=
    twoDirection_unitEigenvector_annihilates_first A B
      hplus hminus 1 (by norm_num) vplus (by simpa using hBvplus)
  have hAvminus : A vminus = 0 :=
    twoDirection_unitEigenvector_annihilates_first A B
      hplus hminus (-1) (by norm_num) vminus (by simpa using hBvminus)
  intro u hu
  rcases hu with rfl | rfl | rfl | rfl
  · simp [hBuplus, hAuplus]
  · simp [hBuminus, hAuminus, map_neg]
  · simp [hAvplus, hBvplus]
  · simp [hAvminus, hBvminus, map_neg]

section FiniteDimensional
variable [FiniteDimensional ℂ E]

/-- An orthonormal quartet spans exactly four complex dimensions. -/
theorem twoDirection_extremalQuartet_span_finrank
    (q : Fin 4 → E) (hq : Orthonormal ℂ q) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range q)) = 4 := by
  simpa using finrank_span_eq_card (Orthonormal.linearIndependent hq)

/-- A four-dimensional orthonormal extremal subspace has a
two-dimensional residual complement in ambient dimension six. -/
theorem twoDirection_sixDim_residual_finrank
    (q : Fin 4 → E) (hq : Orthonormal ℂ q)
    (hDim : Module.finrank ℂ E = 6) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range q))ᗮ = 2 := by
  let S := Submodule.span ℂ (Set.range q)
  have hspan : Module.finrank ℂ S = 4 :=
    twoDirection_extremalQuartet_span_finrank q hq
  change Module.finrank ℂ Sᗮ = 2
  apply Submodule.finrank_add_finrank_orthogonal'
  omega

/-- The analogous residual complement in ambient dimension
seven has three complex dimensions. -/
theorem twoDirection_sevenDim_residual_finrank
    (q : Fin 4 → E) (hq : Orthonormal ℂ q)
    (hDim : Module.finrank ℂ E = 7) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range q))ᗮ = 3 := by
  let S := Submodule.span ℂ (Set.range q)
  have hspan : Module.finrank ℂ S = 4 :=
    twoDirection_extremalQuartet_span_finrank q hq
  change Module.finrank ℂ Sᗮ = 3
  apply Submodule.finrank_add_finrank_orthogonal'
  omega

end FiniteDimensional

end Neoplatonic.LTR
