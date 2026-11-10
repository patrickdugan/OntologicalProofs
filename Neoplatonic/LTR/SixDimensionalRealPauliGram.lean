import Neoplatonic.LTR.SixDimensionalPauliNecessaryBounds
import Mathlib.Tactic

/-!
# LTR-MAN-72: real Pauli Gram constraints in the actual 6D residual

MAN-71 proves both scalar C*-norm inequalities for the two genuine
two-dimensional compressed residual matrices of a six-dimensional
Hamming-coordinate extremal system.

Taking real parts and using |Re(z)| ≤ ‖z‖ combines those two
inequalities into a single real absolute-value bound. This isolates
the invariant sum of quadratic Pauli lengths and the magnitude of
their mixed coefficient.

These quantities are the real Gram data for the vectors representing
traceless Hermitian two-by-two matrices in Pauli coordinates. The
geometric interpretation is used only when Hermitianity and zero
trace are available, as established for the actual residual in MAN-65.
The theorem below does not assert existence of a four-atom exact
Hamming representation.
-/

namespace Neoplatonic.LTR

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The real quadratic Pauli coefficient, interpreted as a squared
length for traceless Hermitian matrices. -/
noncomputable def pauliRealQuadratic (M : TwoMat) : ℝ :=
  (pauliQuadratic M).re

/-- The real mixed Pauli coefficient, equal to twice the Euclidean
inner product of the corresponding Hermitian Pauli vectors. -/
noncomputable def pauliRealMixed (M N : TwoMat) : ℝ :=
  (pauliMixed M N).re

/-- A real-parts consequence of simultaneous complex contraction
inequalities. This lemma applies to arbitrary complex coefficients. -/
theorem complex_simultaneous_real_abs_bound
    (q r c : ℂ)
    (hplus : ‖q + r + c‖ ≤ (1 : ℝ))
    (hminus : ‖q + r - c‖ ≤ (1 : ℝ)) :
    q.re + r.re + |c.re| ≤ 1 := by
  have hp : q.re + r.re + c.re ≤ 1 := by
    have h := (Complex.re_le_norm (q + r + c)).trans hplus
    simpa only [Complex.add_re] using h
  have hm : q.re + r.re - c.re ≤ 1 := by
    have h := (Complex.re_le_norm (q + r - c)).trans hminus
    simpa only [Complex.add_re, Complex.sub_re] using h
  rcases le_total 0 c.re with hc | hc
  · simpa only [abs_of_nonneg hc] using hp
  · rw [abs_of_nonpos hc]
    linarith

/-- Real Pauli Gram bound, derived using the precise MAN-67
plus/minus complex coefficients. -/
theorem twoDim_pauli_realGram_bound
    (M N : TwoMat)
    (hplus : ‖pauliQuadratic M + pauliQuadratic N +
      pauliMixed M N‖ ≤ 1)
    (hminus : ‖pauliQuadratic M + pauliQuadratic N -
      pauliMixed M N‖ ≤ 1) :
    pauliRealQuadratic M + pauliRealQuadratic N +
      |pauliRealMixed M N| ≤ 1 := by
  exact complex_simultaneous_real_abs_bound
    (pauliQuadratic M) (pauliQuadratic N) (pauliMixed M N)
    hplus hminus

/-- The absolute mixed coefficient has a budget determined by the
two Pauli quadratic lengths. -/
theorem twoDim_pauli_realGram_mixed_budget
    (M N : TwoMat)
    (hplus : ‖pauliQuadratic M + pauliQuadratic N +
      pauliMixed M N‖ ≤ 1)
    (hminus : ‖pauliQuadratic M + pauliQuadratic N -
      pauliMixed M N‖ ≤ 1) :
    |pauliRealMixed M N| ≤
      1 - (pauliRealQuadratic M + pauliRealQuadratic N) := by
  have h := twoDim_pauli_realGram_bound M N hplus hminus
  linarith

/-- The two real quadratic coefficients jointly fit in the
unit budget. -/
theorem twoDim_pauli_realGram_energy_budget
    (M N : TwoMat)
    (hplus : ‖pauliQuadratic M + pauliQuadratic N +
      pauliMixed M N‖ ≤ 1)
    (hminus : ‖pauliQuadratic M + pauliQuadratic N -
      pauliMixed M N‖ ≤ 1) :
    pauliRealQuadratic M + pauliRealQuadratic N ≤ 1 := by
  have h := twoDim_pauli_realGram_bound M N hplus hminus
  have hnonneg : 0 ≤ |pauliRealMixed M N| := abs_nonneg _
  linarith

section ActualSixDimensionalResidual

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The genuine 6D residual matrices obey a single real Gram bound.
All norm hypotheses are inherited from MAN-60/68/69/70/71. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_realGram_bound
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    let M := S.sixDimResidualMatrixA hq hDim
    let N := S.sixDimResidualMatrixB hq hDim
    pauliRealQuadratic M + pauliRealQuadratic N +
      |pauliRealMixed M N| ≤ 1 := by
  dsimp
  obtain ⟨hp, hm⟩ :=
    S.sixDimResidual_pauliCoefficients_le_one hq hDim htrA htrB
  exact twoDim_pauli_realGram_bound _ _ hp hm

end ActualSixDimensionalResidual

end Neoplatonic.LTR
