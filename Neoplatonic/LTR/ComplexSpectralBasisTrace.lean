import Neoplatonic.LTR.ComplexSpectralGlobalTrace
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The global standard-basis spectral trace

The earlier global trace proof sums finite-dimensional block traces.
Here the diagonal entries are computed directly against actual vectors
in H = ℓ²(ℕ, ℂ²). Thus the global spectral-power operator itself has
an absolutely summable standard-orthonormal-basis trace for every p > 0.

An abstract Schatten trace-ideal class and the identification with
the full unbounded functional calculus remain separate obligations.
-/

namespace Neoplatonic.LTR

open scoped lp InnerProductSpace

/-- Standard unit vector in the k-th component of the j-th Hilbert block. -/
noncomputable def complexSpectralStandardBasisVector
    (j : ℕ) (k : Fin 2) : ComplexDiracBlockHilbert :=
  lp.single 2 j (EuclideanSpace.single k (1 : ℂ))

/-- Exact diagonal matrix entry of the actual global spectral power
with respect to each standard Hilbert basis vector. -/
theorem chosenComplexSpectralPower_inner_basis
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p)
    (j : ℕ) (k : Fin 2) :
    inner ℂ (complexSpectralStandardBasisVector j k)
        (chosenComplexSpectralPowerCLM scale p hp
          (complexSpectralStandardBasisVector j k)) =
      (complexSpectralPowerWeight scale p j : ℂ) := by
  classical
  unfold complexSpectralStandardBasisVector
  rw [lp.inner_single_left]
  rw [chosenComplexSpectralPowerCLM_apply]
  rw [EuclideanSpace.inner_single_left]
  simp

/-- The two diagonal entries in the j-th Hilbert basis block. -/
noncomputable def complexSpectralBasisBlockTrace
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) (j : ℕ) : ℂ :=
  ∑ k : Fin 2,
    inner ℂ (complexSpectralStandardBasisVector j k)
      (chosenComplexSpectralPowerCLM scale p hp
        (complexSpectralStandardBasisVector j k))

theorem complexSpectralBasisBlockTrace_eq
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) (j : ℕ) :
    complexSpectralBasisBlockTrace scale p hp j =
      (complexSpectralTraceTerm scale p j : ℂ) := by
  simp [complexSpectralBasisBlockTrace,
    chosenComplexSpectralPower_inner_basis,
    Fin.sum_univ_two, complexSpectralTraceTerm,
    complexSpectralPowerWeight, two_mul]

/-- The standard-basis trace of the global spectral-power operator. -/
noncomputable def complexSpectralHilbertBasisTrace
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) : ℂ :=
  ∑' j : ℕ, complexSpectralBasisBlockTrace scale p hp j

/-- The global operator's actual standard-basis diagonal is summable. -/
theorem complexSpectralBasisBlockTrace_summable
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    Summable (complexSpectralBasisBlockTrace scale p hp) := by
  have hs : Summable (fun j : ℕ =>
      (complexSpectralTraceTerm scale p j : ℂ)) :=
    (RCLike.summable_ofReal (𝕜 := ℂ)).2
      (complexSpectralTraceTerm_summable scale p hp)
  have hfun : complexSpectralBasisBlockTrace scale p hp =
      (fun j : ℕ => (complexSpectralTraceTerm scale p j : ℂ)) := by
    funext j
    exact complexSpectralBasisBlockTrace_eq scale p hp j
  rw [hfun]
  exact hs

/-- The infinite trace of actual Hilbert-basis diagonal entries is
exactly the convergent scalar spectral-energy series. -/
theorem complexSpectralHilbertBasisTrace_eq
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    complexSpectralHilbertBasisTrace scale p hp =
      (complexSpectralGlobalTrace scale p : ℂ) := by
  calc
    complexSpectralHilbertBasisTrace scale p hp =
        ∑' j : ℕ, (complexSpectralTraceTerm scale p j : ℂ) := by
          simp only [complexSpectralHilbertBasisTrace,
            complexSpectralBasisBlockTrace_eq]
    _ = (complexSpectralGlobalTrace scale p : ℂ) := by
          simp only [complexSpectralGlobalTrace, Complex.ofReal_tsum]

end Neoplatonic.LTR
