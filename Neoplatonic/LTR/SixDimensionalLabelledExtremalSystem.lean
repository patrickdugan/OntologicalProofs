import Neoplatonic.LTR.SixDimensionalMixedTraceBridge
import Neoplatonic.LTR.FiveFibreCanonicalNoGo
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# LTR-MAN-76: genuine six-dimensional labelled Dirac extremal system

MAN-74 supplies coordinate projections and the Hermitian commutators
A = i[D,P] and B = i[D,Q] in every labelled diagonal chart. This file
builds the grading, Hilbert-operator, and signed eigenquartet structures
needed to instantiate MAN-75 and its two-dimensional Pauli Gram result
in the actual six-dimensional chart.

The spectral hypotheses supplied to the construction are precisely
the operator norm-one and simultaneous contraction certificates. The
next part connects these certificates with exact Connes-dual Hamming
distance witnesses, without assuming any arbitrary preexisting
extremal eigenvectors.
-/

namespace Neoplatonic.LTR

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Each Boolean first-coordinate projection is genuinely idempotent. -/
theorem sixLabelledSquareP_idempotent
    (label : Fin 6 → Fin 4) :
    labelledSquarePMatrix label * labelledSquarePMatrix label =
      labelledSquarePMatrix label := by
  change Matrix.diagonal (fun i => squareTruthBitP (label i)) *
      Matrix.diagonal (fun i => squareTruthBitP (label i)) =
        Matrix.diagonal (fun i => squareTruthBitP (label i))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have h : ∀ v : Fin 4,
      squareTruthBitP v * squareTruthBitP v = squareTruthBitP v := by
    intro v
    fin_cases v <;> norm_num [squareTruthBitP]
  exact h (label i)

/-- The second coordinate projection is idempotent in the same chart. -/
theorem sixLabelledSquareQ_idempotent
    (label : Fin 6 → Fin 4) :
    labelledSquareQMatrix label * labelledSquareQMatrix label =
      labelledSquareQMatrix label := by
  change Matrix.diagonal (fun i => squareTruthBitQ (label i)) *
      Matrix.diagonal (fun i => squareTruthBitQ (label i)) =
        Matrix.diagonal (fun i => squareTruthBitQ (label i))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have h : ∀ v : Fin 4,
      squareTruthBitQ v * squareTruthBitQ v = squareTruthBitQ v := by
    intro v
    fin_cases v <;> norm_num [squareTruthBitQ]
  exact h (label i)

/-- The first truth-coordinate projection is self-adjoint. -/
theorem sixLabelledSquareP_selfAdjoint
    (label : Fin 6 → Fin 4) :
    IsSelfAdjoint (labelledSquarePMatrix label) := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  change IsSelfAdjoint (squareTruthBitP (label i))
  have h : ∀ v : Fin 4, IsSelfAdjoint (squareTruthBitP v) := by
    intro v
    fin_cases v <;> simp [squareTruthBitP, IsSelfAdjoint]
  exact h _

/-- The second truth-coordinate projection is self-adjoint. -/
theorem sixLabelledSquareQ_selfAdjoint
    (label : Fin 6 → Fin 4) :
    IsSelfAdjoint (labelledSquareQMatrix label) := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  change IsSelfAdjoint (squareTruthBitQ (label i))
  have h : ∀ v : Fin 4, IsSelfAdjoint (squareTruthBitQ v) := by
    intro v
    fin_cases v <;> simp [squareTruthBitQ, IsSelfAdjoint]
  exact h _

/-- For a Hermitian six-dimensional Dirac matrix, the actual
first imaginary coordinate commutator is self-adjoint. -/
theorem sixLabelledSquareA_selfAdjoint
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    IsSelfAdjoint (labelledSquareA label D) := by
  have hDSelf : IsSelfAdjoint D :=
    (Matrix.IsHermitian.ext fun i j => (hD i j).symm).isSelfAdjoint
  have hC : D * labelledSquarePMatrix label -
        labelledSquarePMatrix label * D ∈
      skewAdjoint (Matrix (Fin 6) (Fin 6) ℂ) := by
    rw [skewAdjoint.mem_iff]
    simp only [star_sub, star_mul, hDSelf.star_eq,
      (sixLabelledSquareP_selfAdjoint label).star_eq]
    abel
  rw [labelledSquareA_eq_diagonal_commutator]
  exact Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint.mpr hC

/-- The second actual imaginary coordinate commutator is self-adjoint. -/
theorem sixLabelledSquareB_selfAdjoint
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    IsSelfAdjoint (labelledSquareB label D) := by
  have hDSelf : IsSelfAdjoint D :=
    (Matrix.IsHermitian.ext fun i j => (hD i j).symm).isSelfAdjoint
  have hC : D * labelledSquareQMatrix label -
        labelledSquareQMatrix label * D ∈
      skewAdjoint (Matrix (Fin 6) (Fin 6) ℂ) := by
    rw [skewAdjoint.mem_iff]
    simp only [star_sub, star_mul, hDSelf.star_eq,
      (sixLabelledSquareQ_selfAdjoint label).star_eq]
    abel
  rw [labelledSquareB_eq_diagonal_commutator]
  exact Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint.mpr hC

/-- Literal first coordinate grading from the Boolean projector. -/
def sixLabelledSquareGradeP (label : Fin 6 → Fin 4) : SixMat :=
  2 * labelledSquarePMatrix label - 1

/-- Literal second coordinate grading from the Boolean projector. -/
def sixLabelledSquareGradeQ (label : Fin 6 → Fin 4) : SixMat :=
  2 * labelledSquareQMatrix label - 1

theorem sixLabelledSquareGradeP_square_one
    (label : Fin 6 → Fin 4) :
    sixLabelledSquareGradeP label *
      sixLabelledSquareGradeP label = 1 :=
  idempotent_grading_square_one
    (labelledSquarePMatrix label)
    (sixLabelledSquareP_idempotent label)

theorem sixLabelledSquareGradeQ_square_one
    (label : Fin 6 → Fin 4) :
    sixLabelledSquareGradeQ label *
      sixLabelledSquareGradeQ label = 1 :=
  idempotent_grading_square_one
    (labelledSquareQMatrix label)
    (sixLabelledSquareQ_idempotent label)

/-- The first grading anticommutes with the actual first coordinate
commutator for *any* Dirac matrix. -/
theorem sixLabelledSquareGradeP_anticommutes
    (label : Fin 6 → Fin 4) (D : SixMat) :
    sixLabelledSquareGradeP label * labelledSquareA label D =
      -(labelledSquareA label D * sixLabelledSquareGradeP label) := by
  let P := labelledSquarePMatrix label
  let C := D * P - P * D
  let G := 2 * P - 1
  have hp : P * P = P := sixLabelledSquareP_idempotent label
  have hcomm : G * C = -(C * G) :=
    idempotent_grading_commutator_anticommutes D P hp
  have hA : labelledSquareA label D = Complex.I • C := by
    simpa [P, C] using labelledSquareA_eq_diagonal_commutator label D
  change G * labelledSquareA label D =
      -(labelledSquareA label D * G)
  rw [hA]
  calc
    G * (Complex.I • C) = Complex.I • (G * C) := by
      rw [mul_smul_comm]
    _ = Complex.I • (-(C * G)) := by rw [hcomm]
    _ = -((Complex.I • C) * G) := by
      simp only [smul_neg, smul_mul_assoc]

/-- The second grading anticommutes with the actual second coordinate
commutator. -/
theorem sixLabelledSquareGradeQ_anticommutes
    (label : Fin 6 → Fin 4) (D : SixMat) :
    sixLabelledSquareGradeQ label * labelledSquareB label D =
      -(labelledSquareB label D * sixLabelledSquareGradeQ label) := by
  let P := labelledSquareQMatrix label
  let C := D * P - P * D
  let G := 2 * P - 1
  have hp : P * P = P := sixLabelledSquareQ_idempotent label
  have hcomm : G * C = -(C * G) :=
    idempotent_grading_commutator_anticommutes D P hp
  have hA : labelledSquareB label D = Complex.I • C := by
    simpa [P, C] using labelledSquareB_eq_diagonal_commutator label D
  change G * labelledSquareB label D =
      -(labelledSquareB label D * G)
  rw [hA]
  calc
    G * (Complex.I • C) = Complex.I • (G * C) := by
      rw [mul_smul_comm]
    _ = Complex.I • (-(C * G)) := by rw [hcomm]
    _ = -((Complex.I • C) * G) := by
      simp only [smul_neg, smul_mul_assoc]

/-- The actual continuous Hilbert operators of the labelled
six-dimensional coordinate commutators. -/
noncomputable def sixLabelledAOperator
    (label : Fin 6 → Fin 4) (D : SixMat) : SixH →L[ℂ] SixH :=
  (labelledSquareA label D).toEuclideanLin.toContinuousLinearMap

noncomputable def sixLabelledBOperator
    (label : Fin 6 → Fin 4) (D : SixMat) : SixH →L[ℂ] SixH :=
  (labelledSquareB label D).toEuclideanLin.toContinuousLinearMap

/-- The labelled first coordinate commutator is a genuine
self-adjoint bounded Hilbert operator. -/
theorem sixLabelledAOperator_selfAdjoint
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    IsSelfAdjoint (sixLabelledAOperator label D) :=
by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (sixLabelledSquareA_selfAdjoint label D hD))

/-- The labelled second coordinate commutator is self-adjoint. -/
theorem sixLabelledBOperator_selfAdjoint
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    IsSelfAdjoint (sixLabelledBOperator label D) :=
by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (sixLabelledSquareB_selfAdjoint label D hD))

/-- The actual labelled Dirac pair satisfies the MAN-58
signed-eigenquartet hypotheses whenever the two coordinate norms
equal one and the opposite witnesses give simultaneous contractions.
The resulting true spectral pair uses exactly the same Dirac matrix. -/
theorem sixLabelledSquare_exists_extremalSystem
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hplus : ‖sixLabelledAOperator label D +
      sixLabelledBOperator label D‖ ≤ 1)
    (hminus : ‖sixLabelledAOperator label D -
      sixLabelledBOperator label D‖ ≤ 1)
    (hAnorm : ‖sixLabelledAOperator label D‖ = 1)
    (hBnorm : ‖sixLabelledBOperator label D‖ = 1) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus) ∧
      S.A = sixLabelledAOperator label D ∧
      S.B = sixLabelledBOperator label D := by
  let A : SixH →L[ℂ] SixH := sixLabelledAOperator label D
  let B : SixH →L[ℂ] SixH := sixLabelledBOperator label D
  let GA : SixH →ₗ[ℂ] SixH := (sixLabelledSquareGradeP label).toEuclideanLin
  let GB : SixH →ₗ[ℂ] SixH := (sixLabelledSquareGradeQ label).toEuclideanLin
  have hSA : IsSelfAdjoint A := sixLabelledAOperator_selfAdjoint label D hD
  have hSB : IsSelfAdjoint B := sixLabelledBOperator_selfAdjoint label D hD
  have hGA : GA.comp GA = LinearMap.id := by
    have h := congrArg
      (fun M : SixMat => M.toEuclideanLin)
      (sixLabelledSquareGradeP_square_one label)
    simpa [GA, fiveFibreSquare_toEuclidean_mul, Matrix.toLpLin_one] using h
  have hGB : GB.comp GB = LinearMap.id := by
    have h := congrArg
      (fun M : SixMat => M.toEuclideanLin)
      (sixLabelledSquareGradeQ_square_one label)
    simpa [GB, fiveFibreSquare_toEuclidean_mul, Matrix.toLpLin_one] using h
  have hAG : A.toLinearMap.comp GA = -(GA.comp A.toLinearMap) := by
    have hm : labelledSquareA label D * sixLabelledSquareGradeP label =
        -(sixLabelledSquareGradeP label * labelledSquareA label D) := by
      rw [sixLabelledSquareGradeP_anticommutes]
      simp
    have h := congrArg (fun M : SixMat => M.toEuclideanLin) hm
    simpa [A, GA, sixLabelledAOperator, fiveFibreSquare_toEuclidean_mul] using h
  have hBG : B.toLinearMap.comp GB = -(GB.comp B.toLinearMap) := by
    have hm : labelledSquareB label D * sixLabelledSquareGradeQ label =
        -(sixLabelledSquareGradeQ label * labelledSquareB label D) := by
      rw [sixLabelledSquareGradeQ_anticommutes]
      simp
    have h := congrArg (fun M : SixMat => M.toEuclideanLin) hm
    simpa [B, GB, sixLabelledBOperator, fiveFibreSquare_toEuclidean_mul] using h
  obtain ⟨q, hq, hq0, hq1, hq2, hq3⟩ :=
    twoDirection_gradedCoordinates_exists_orthonormalQuartet
      A B GA GB hplus hminus hSA hSB hAnorm hBnorm
      hGA hGB hAG hBG
  have hq' : Orthonormal ℂ
      (twoDirectionSignedQuartet (q 0) (q 1) (q 2) (q 3)) := by
    have heq :
        twoDirectionSignedQuartet (q 0) (q 1) (q 2) (q 3) = q := by
      funext i
      fin_cases i <;> simp [twoDirectionSignedQuartet]
    rw [heq]
    exact hq
  refine ⟨{
    A := A, B := B,
    uplus := q 0, uminus := q 1, vplus := q 2, vminus := q 3,
    plus_le := hplus, minus_le := hminus,
    A_self := hSA, B_self := hSB,
    A_uplus := hq0, A_uminus := hq1,
    B_vplus := hq2, B_vminus := hq3
  }, hq', rfl, rfl⟩

end Neoplatonic.LTR
