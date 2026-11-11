import Neoplatonic.LTR.SixDimensionalTriple03ProbeHammingNoGo
import Mathlib.Tactic

/-!
# LTR-MAN-111: mirrored triple-corner separating probe at truth atom 11

The positive saturated corner has active truth fibres 00 and 11.
When all 11-to-neutral Dirac entries vanish, the real observable
g=(2,3,3,0) has an imaginary commutator equal to a diagonal sign
conjugate of W+=A+B. The conjugating sign J equals -1 on atom 11
and +1 on every other truth atom. The sign identity holds entrywise
in the actual labelled six-dimensional Hilbert chart.

The resulting imaginary commutator has norm one because W+ is
a Hermitian involution. Yet the probe separates atom 11 from
atoms 01 and 10 by 3, contradicting their Hamming distance 1.
The zero 11-to-neutral Dirac support hypothesis is kept explicit.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The mirrored triple-corner probe, with values (2,3,3,0)
on truth atoms (00,01,10,11). -/
def squareTriple11Probe (u : Fin 4) : ℂ :=
  if u = 3 then 0 else if u = 0 then 2 else 3

/-- A sign change on truth atom 11, leaving the other atoms fixed. -/
def squareTriple11Sign (u : Fin 4) : ℂ :=
  if u = 3 then -1 else 1

/-- Exactly the 11-neutral truth edges on which the probe
coefficient differs from the signed Hamming-sum coefficient. -/
def squareTriple11Bad (u v : Fin 4) : Prop :=
  (u = 3 ∧ (v = 1 ∨ v = 2)) ∨
    (v = 3 ∧ (u = 1 ∨ u = 2))

/-- Outside 11-neutral edges, the mirrored probe's coefficient
is the Hamming-sum coefficient conjugated by its truth signs. -/
theorem squareTriple11Probe_coefficient_of_notBad
    (u v : Fin 4)
    (hbad : ¬ squareTriple11Bad u v) :
    squareTriple11Probe v - squareTriple11Probe u =
      (squareTriple11Sign u * squareTriple11Sign v) *
        ((squareTruthBitP v + squareTruthBitQ v) -
          (squareTruthBitP u + squareTruthBitQ u)) := by
  fin_cases u <;> fin_cases v <;>
    simp_all [squareTriple11Bad, squareTriple11Probe,
      squareTriple11Sign, squareTruthBitP, squareTruthBitQ] <;> ring

/-- The mirrored truth sign squares to one on every atom. -/
theorem squareTriple11Sign_square_one (u : Fin 4) :
    squareTriple11Sign u * squareTriple11Sign u = 1 := by
  fin_cases u <;>
    norm_num [squareTriple11Sign]

/-- Mirrored diagonal sign matrix in the original six-dimensional chart. -/
def sixTriple11SignMatrix (label : Fin 6 → Fin 4) : SixMat :=
  Matrix.diagonal (fun i => squareTriple11Sign (label i))

/-- The mirrored sign matrix is an involution for every label map. -/
theorem sixTriple11SignMatrix_involution
    (label : Fin 6 → Fin 4) :
    sixTriple11SignMatrix label * sixTriple11SignMatrix label = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [sixTriple11SignMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_apply, squareTriple11Sign_square_one,
      Matrix.one_apply]
  · simp [sixTriple11SignMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_apply, Matrix.one_apply, hij]

/-- Hermitianity of the mirrored sign matrix. -/
theorem sixTriple11SignMatrix_hermitian
    (label : Fin 6 → Fin 4) :
    (sixTriple11SignMatrix label).IsHermitian := by
  change (Matrix.diagonal (fun i : Fin 6 =>
    squareTriple11Sign (label i))).IsHermitian
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  change IsSelfAdjoint (squareTriple11Sign (label i))
  by_cases hi : label i = 3 <;>
    simp [squareTriple11Sign, hi, IsSelfAdjoint]

/-- Imaginary commutator of the mirrored triple-fibre separator. -/
def sixTriple11ProbeImagComm
    (label : Fin 6 → Fin 4) (D : SixMat) : SixMat :=
  fun i j => Complex.I *
    (squareTriple11Probe (label j) -
      squareTriple11Probe (label i)) * D i j

/-- Under absence of 11-neutral Dirac edges, the true probe
commutator is the sign conjugate of the positive saturated witness. -/
theorem sixTriple11Probe_signConjugate_plusWitness
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hzero : ∀ i j : Fin 6,
      squareTriple11Bad (label i) (label j) → D i j = 0) :
    sixTriple11ProbeImagComm label D =
      sixTriple11SignMatrix label *
        (labelledSquareA label D + labelledSquareB label D) *
          sixTriple11SignMatrix label := by
  ext i j
  simp only [sixTriple11ProbeImagComm, sixTriple11SignMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.add_apply, labelledSquareA, labelledSquareB]
  by_cases hbad : squareTriple11Bad (label i) (label j)
  · simp [hzero i j hbad]
  · have hc := squareTriple11Probe_coefficient_of_notBad
      (label i) (label j) hbad
    rw [hc]
    ring

/-- Relating the mirrored imaginary probe to its true
Euclidean Hilbert Dirac commutator. -/
theorem sixTriple11ProbeImagComm_eq_iDirac
    (label : Fin 6 → Fin 4) (D : SixMat) :
    sixTriple11ProbeImagComm label D =
      Complex.I •
        (D * Matrix.diagonal (fun i =>
          squareTriple11Probe (label i)) -
        Matrix.diagonal (fun i =>
          squareTriple11Probe (label i)) * D) := by
  ext i j
  simp [sixTriple11ProbeImagComm, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The mirrored probe gives a gap three along the 11-01 edge. -/
theorem squareTriple11Probe_gap31 :
    squareTriple11Probe 1 - squareTriple11Probe 3 = (3 : ℂ) := by
  norm_num [squareTriple11Probe]

/-- Likewise along the 11-10 edge. -/
theorem squareTriple11Probe_gap32 :
    squareTriple11Probe 2 - squareTriple11Probe 3 = (3 : ℂ) := by
  norm_num [squareTriple11Probe]

/-- The mirrored triple separator contradicts exact Hamming
geometry whenever positive saturation and 11-neutral
Dirac support extinction both hold. -/
theorem sixLabelled_exactHamming_saturated03_zeroNeutral11Rows_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hzero : ∀ i j : Fin 6,
      squareTriple11Bad (label i) (label j) → D i j = 0) :
    False := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let J : SixMat := sixTriple11SignMatrix label
  have hW : W * W = 1 :=
    sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution
      label D hD hham h03 h12
  have hWH : W.IsHermitian :=
    sixLabelled_plusWitness_isHermitian label D hD
  have hJ : J * J = 1 :=
    sixTriple11SignMatrix_involution label
  have hJH : J.IsHermitian :=
    sixTriple11SignMatrix_hermitian label
  have hProbe : sixTriple11ProbeImagComm label D = J * W * J :=
    sixTriple11Probe_signConjugate_plusWitness label D hzero
  have hKnorm :
      ‖sixTriple11ProbeImagComm label D‖ = (1 : ℝ) := by
    rw [hProbe]
    exact sixMatrix_hermitianInvolution_signConjugate_norm_one
      W J hW hWH hJ hJH
  have hKop :
      ‖(sixTriple11ProbeImagComm label D).toEuclideanLin.toContinuousLinearMap‖ =
        (1 : ℝ) := by
    change ‖sixTriple11ProbeImagComm label D‖ = (1 : ℝ)
    exact hKnorm
  have hDiracNorm :
      ‖sixLabelledDiracComm label D squareTriple11Probe‖ =
        (1 : ℝ) := by
    rw [sixTriple11ProbeImagComm_eq_iDirac,
      sixLabelled_imaginaryOperator_norm] at hKop
    exact hKop
  have hd31 : sixLabelledConnesDistance label D 3 1 = 1 := by
    simpa [twoBitSquareHamming] using hham 3 1
  have hBound : ‖squareTriple11Probe 3 -
      squareTriple11Probe 1‖ ≤ (1 : ℝ) :=
    sixLabelledConnesDistance_bounds label D 3 1 1
      (by simpa [hd31]) squareTriple11Probe
      (le_of_eq hDiracNorm)
  norm_num [squareTriple11Probe] at hBound

end Neoplatonic.LTR
