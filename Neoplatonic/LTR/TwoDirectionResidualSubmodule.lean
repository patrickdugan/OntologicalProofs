import Neoplatonic.LTR.TwoDirectionResidualReduction
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic

/-!
# LTR-MAN-59: the extremal residual is a genuine invariant Hilbert submodule

MAN-56 shows the signed coordinate operators preserve the four
orthogonality equations and computes the dimensions of the orthogonal
complement of an orthonormal quartet. The present module identifies
those equations with actual membership in the orthogonal submodule
of the quartet's span.

Consequently both bounded coordinate operators, and their ordered
products, preserve this same residual submodule. Its complex
dimension is exactly two or three in ambient dimensions six or
seven when the extremal quartet is orthonormal.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Orthogonality to a finite generating family exactly
characterizes the orthogonal complement of its span. -/
theorem finiteQuartet_mem_orthogonalSpan_iff
    (q : Fin 4 → E) (x : E) :
    x ∈ (Submodule.span ℂ (Set.range q))ᗮ ↔
      ∀ i : Fin 4, inner ℂ (q i) x = 0 := by
  classical
  constructor
  · intro hx i
    exact ((Submodule.span ℂ (Set.range q)).mem_orthogonal x).mp hx
      (q i) (Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    apply ((Submodule.span ℂ (Set.range q)).mem_orthogonal x).mpr
    intro y hy
    refine Submodule.span_induction (p := fun z _ => inner ℂ z x = 0)
      ?_ ?_ (fun u v _ _ hu hv => ?_) (fun a u _ hu => ?_) hy
    · rintro z ⟨i, rfl⟩
      exact h i
    · simp
    · simpa only [inner_add_left, hu, hv, add_zero]
    · simpa [inner_smul_left, hu]

/-- Ordered quartet of the two coordinate operators' extremal
unit eigenvectors. -/
def twoDirectionSignedQuartet
    (uplus uminus vplus vminus : E) : Fin 4 → E :=
  fun i => if i = 0 then uplus else if i = 1 then uminus
    else if i = 2 then vplus else vminus

/-- The common residual subspace is the orthogonal complement
of the span of the extremal quartet. -/
noncomputable def twoDirectionResidualSubmodule
    (uplus uminus vplus vminus : E) : Submodule ℂ E :=
  (Submodule.span ℂ
    (Set.range (twoDirectionSignedQuartet uplus uminus vplus vminus)))ᗮ

/-- MAN-56's four residual orthogonality equations are equivalent
to membership in this concrete linear Hilbert subspace. -/
theorem twoDirectionResidualSubmodule_mem_iff
    (uplus uminus vplus vminus x : E) :
    x ∈ twoDirectionResidualSubmodule uplus uminus vplus vminus ↔
      twoDirectionExtremalResidual uplus uminus vplus vminus x := by
  change x ∈ (Submodule.span ℂ
    (Set.range (twoDirectionSignedQuartet uplus uminus vplus vminus)))ᗮ ↔ _
  rw [finiteQuartet_mem_orthogonalSpan_iff]
  constructor
  · intro h
    exact ⟨by simpa [twoDirectionSignedQuartet] using h 0,
      by simpa [twoDirectionSignedQuartet] using h 1,
      by simpa [twoDirectionSignedQuartet] using h 2,
      by simpa [twoDirectionSignedQuartet] using h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i
    · simpa [twoDirectionSignedQuartet] using h0
    · simpa [twoDirectionSignedQuartet] using h1
    · simpa [twoDirectionSignedQuartet] using h2
    · simpa [twoDirectionSignedQuartet] using h3

/-- The actual residual Hilbert submodule is invariant under both
self-adjoint Hamming coordinate operators. -/
theorem twoDirection_residualSubmodule_invariant
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (hAself : IsSelfAdjoint A) (hBself : IsSelfAdjoint B)
    (uplus uminus vplus vminus : E)
    (hAuplus : A uplus = uplus)
    (hAuminus : A uminus = -uminus)
    (hBvplus : B vplus = vplus)
    (hBvminus : B vminus = -vminus)
    (x : E)
    (hx : x ∈ twoDirectionResidualSubmodule
      uplus uminus vplus vminus) :
    A x ∈ twoDirectionResidualSubmodule uplus uminus vplus vminus ∧
    B x ∈ twoDirectionResidualSubmodule uplus uminus vplus vminus := by
  have hres :
      twoDirectionExtremalResidual uplus uminus vplus vminus x :=
    (twoDirectionResidualSubmodule_mem_iff
      uplus uminus vplus vminus x).mp hx
  obtain ⟨hAx, hBx⟩ :=
    twoDirection_extremalResidual_invariant A B hplus hminus
      hAself hBself uplus uminus vplus vminus x
      hAuplus hAuminus hBvplus hBvminus hres
  exact ⟨(twoDirectionResidualSubmodule_mem_iff
      uplus uminus vplus vminus (A x)).mpr hAx,
    (twoDirectionResidualSubmodule_mem_iff
      uplus uminus vplus vminus (B x)).mpr hBx⟩

/-- The ordered products of the two coordinate operators map the
residual submodule back into itself. -/
theorem twoDirection_residualSubmodule_products_invariant
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (hAself : IsSelfAdjoint A) (hBself : IsSelfAdjoint B)
    (uplus uminus vplus vminus : E)
    (hAuplus : A uplus = uplus)
    (hAuminus : A uminus = -uminus)
    (hBvplus : B vplus = vplus)
    (hBvminus : B vminus = -vminus)
    (x : E)
    (hx : x ∈ twoDirectionResidualSubmodule
      uplus uminus vplus vminus) :
    A (B x) ∈ twoDirectionResidualSubmodule uplus uminus vplus vminus ∧
    B (A x) ∈ twoDirectionResidualSubmodule uplus uminus vplus vminus := by
  have hab := twoDirection_residualSubmodule_invariant
    A B hplus hminus hAself hBself
    uplus uminus vplus vminus
    hAuplus hAuminus hBvplus hBvminus x hx
  exact ⟨(twoDirection_residualSubmodule_invariant
      A B hplus hminus hAself hBself
      uplus uminus vplus vminus
      hAuplus hAuminus hBvplus hBvminus
      (B x) hab.2).1,
    (twoDirection_residualSubmodule_invariant
      A B hplus hminus hAself hBself
      uplus uminus vplus vminus
      hAuplus hAuminus hBvplus hBvminus
      (A x) hab.1).2⟩

section FiniteDimensional
variable [FiniteDimensional ℂ E]

/-- The genuine extremal residual Hilbert submodule has complex
dimension two in an ambient six-dimensional space. -/
theorem twoDirection_sixDim_signedResidual_finrank
    (uplus uminus vplus vminus : E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet uplus uminus vplus vminus))
    (hDim : Module.finrank ℂ E = 6) :
    Module.finrank ℂ
      (twoDirectionResidualSubmodule uplus uminus vplus vminus) = 2 := by
  change Module.finrank ℂ
    (Submodule.span ℂ
      (Set.range (twoDirectionSignedQuartet uplus uminus vplus vminus)))ᗮ = 2
  exact twoDirection_sixDim_residual_finrank
    (twoDirectionSignedQuartet uplus uminus vplus vminus) hq hDim

/-- The genuine extremal residual Hilbert submodule has complex
dimension three in an ambient seven-dimensional space. -/
theorem twoDirection_sevenDim_signedResidual_finrank
    (uplus uminus vplus vminus : E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet uplus uminus vplus vminus))
    (hDim : Module.finrank ℂ E = 7) :
    Module.finrank ℂ
      (twoDirectionResidualSubmodule uplus uminus vplus vminus) = 3 := by
  change Module.finrank ℂ
    (Submodule.span ℂ
      (Set.range (twoDirectionSignedQuartet uplus uminus vplus vminus)))ᗮ = 3
  exact twoDirection_sevenDim_residual_finrank
    (twoDirectionSignedQuartet uplus uminus vplus vminus) hq hDim

end FiniteDimensional

end Neoplatonic.LTR
