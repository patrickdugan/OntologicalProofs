import Neoplatonic.LTR.SixDimensionalTriple03SeparatingProbe
import Neoplatonic.LTR.SixDimensionalExactHammingAmbientInvolution
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-108: the triple-fibre separating probe violates a Hamming edge

MAN-107 proves that for the probe f=(0,3,3,2), when all
00-to-neutral Dirac entries vanish, its imaginary commutator
K=i[D,f] equals J W+ J for an involutive diagonal sign matrix J.

The exact Hamming saturation of MAN-91 proves W+²=I₆.
When the Dirac matrix is Hermitian, W+ and J are Hermitian,
so K is a Hermitian involution and its genuine Euclidean
operator norm is exactly one.

But f(01)-f(00)=3, contradicting the exact Hamming edge
distance d(00,01)=1 via the Connes dual definition.

The zero 00-to-neutral support premise is still explicit here;
MAN-106 is the required independent bridge from a singleton
00 fibre to that support premise. No general six-dimensional
no-go is claimed without discharging it.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The signed truth diagonal is Hermitian in every labelled
six-dimensional complex Hilbert chart. -/
theorem sixTriple03SignMatrix_hermitian
    (label : Fin 6 → Fin 4) :
    (sixTriple03SignMatrix label).IsHermitian := by
  change (Matrix.diagonal (fun i : Fin 6 =>
    squareTriple03Sign (label i))).IsHermitian
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  change IsSelfAdjoint (squareTriple03Sign (label i))
  by_cases hi : label i = 1 ∨ label i = 2 <;>
    simp [squareTriple03Sign, hi, IsSelfAdjoint]

/-- A complex Hermitian matrix squaring to the identity has
exactly unit Euclidean operator norm. -/
theorem sixMatrix_hermitianInvolution_operatorNorm_one
    (M : SixMat) (hH : M.IsHermitian) (hM : M * M = 1) :
    ‖M‖ = (1 : ℝ) := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self M
  rw [hH.eq, hM] at h
  have hs : ‖M‖ * ‖M‖ = (1 : ℝ) := by
    simpa using h.symm
  nlinarith [norm_nonneg M]

/-- Conjugating a Hermitian involution by a second Hermitian
involution preserves its exact unit operator norm. -/
theorem sixMatrix_hermitianInvolution_signConjugate_norm_one
    (W J : SixMat)
    (hW : W * W = 1) (hWH : W.IsHermitian)
    (hJ : J * J = 1) (hJH : J.IsHermitian) :
    ‖J * W * J‖ = (1 : ℝ) := by
  have hHerm : (J * W * J).IsHermitian := by
    change (J * W * J).conjTranspose = J * W * J
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hJH.eq, hWH.eq]
    noncomm_ring
  have hSq : (J * W * J) * (J * W * J) = 1 := by
    calc
      (J * W * J) * (J * W * J) =
          J * (W * (J * J) * W) * J := by noncomm_ring
      _ = J * (W * W) * J := by rw [hJ]; simp
      _ = J * J := by rw [hW]; simp
      _ = 1 := hJ
  exact sixMatrix_hermitianInvolution_operatorNorm_one
    (J * W * J) hHerm hSq

/-- The imaginary triple-probe commutator is exactly i times
the ordinary original six-dimensional Dirac commutator matrix. -/
theorem sixTriple03ProbeImagComm_eq_iDirac
    (label : Fin 6 → Fin 4) (D : SixMat) :
    sixTriple03ProbeImagComm label D =
      Complex.I •
        (D * Matrix.diagonal (fun i =>
          squareTriple03Probe (label i)) -
        Matrix.diagonal (fun i =>
          squareTriple03Probe (label i)) * D) := by
  ext i j
  simp [sixTriple03ProbeImagComm, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- If positive saturation holds and all 00-to-neutral
Dirac entries vanish, the separating probe has unit Dirac
Lipschitz seminorm despite a three-unit Hamming edge gap.
This contradicts exact two-bit Hamming distances. -/
theorem sixLabelled_exactHamming_saturated03_zeroNeutralRows_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hzero : ∀ i j : Fin 6,
      squareTriple03Bad (label i) (label j) → D i j = 0) :
    False := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let J : SixMat := sixTriple03SignMatrix label
  have hW : W * W = 1 :=
    sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution
      label D hD hham h03 h12
  have hWH : W.IsHermitian :=
    sixLabelled_plusWitness_isHermitian label D hD
  have hJ : J * J = 1 :=
    sixTriple03SignMatrix_involution label
  have hJH : J.IsHermitian :=
    sixTriple03SignMatrix_hermitian label
  have hProbe :
      sixTriple03ProbeImagComm label D = J * W * J :=
    sixTriple03Probe_signConjugate_plusWitness label D hzero
  have hKnorm :
      ‖sixTriple03ProbeImagComm label D‖ = (1 : ℝ) := by
    rw [hProbe]
    exact sixMatrix_hermitianInvolution_signConjugate_norm_one
      W J hW hWH hJ hJH
  have hKop :
      ‖(sixTriple03ProbeImagComm label D).toEuclideanLin.toContinuousLinearMap‖ =
        (1 : ℝ) := by
    change ‖sixTriple03ProbeImagComm label D‖ = (1 : ℝ)
    exact hKnorm
  have hDiracNorm :
      ‖sixLabelledDiracComm label D squareTriple03Probe‖ =
        (1 : ℝ) := by
    rw [sixTriple03ProbeImagComm_eq_iDirac,
      sixLabelled_imaginaryOperator_norm] at hKop
    exact hKop
  have hd01 : sixLabelledConnesDistance label D 0 1 = 1 := by
    simpa [twoBitSquareHamming] using hham 0 1
  have hBound : ‖squareTriple03Probe 0 -
      squareTriple03Probe 1‖ ≤ (1 : ℝ) :=
    sixLabelledConnesDistance_bounds label D 0 1 1
      (by simpa [hd01]) squareTriple03Probe
      (le_of_eq hDiracNorm)
  norm_num [squareTriple03Probe] at hBound

end Neoplatonic.LTR
