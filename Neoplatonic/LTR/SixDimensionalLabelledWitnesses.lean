import Neoplatonic.LTR.SixDimensionalLabelledExtremalSystem
import Neoplatonic.LTR.FiveFibreConnesDualDistance
import Mathlib.Tactic

/-!
# LTR-MAN-76: actual Connes Hamming witnesses feed six-dimensional spectra

The four truth values f : Fin 4 → ℂ act by the literal diagonal
matrix diag (f ∘ label) on the same six-dimensional Hilbert space
as a Hermitian Dirac operator D.

The two exact opposite-corner Hamming observables
(0,1,1,2) and (1,0,2,1) have commutators proportional to
A+B and B-A, where A=i[D,P] and B=i[D,Q]. Their genuine
Hilbert commutator bounds give the two simultaneous contractions.

A finite Connes dual unit-edge upper bound forces the individual
coordinate commutators to have norm ≥1 by rescaling an observable.
Together with the two witness contractions, they have norm exactly
one. This closes the bridge to MAN-58's actual signed quartet
construction without supplying quartet vectors as assumptions.

The theorem assumes unit-admissibility of the two explicit opposite
witnesses. A separate finite compactness argument promotes exact
opposite-corner dual suprema to the existence of these witnesses.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The literal represented Dirac commutator of four complex truth
values, as a genuine six-dimensional continuous Hilbert operator. -/
noncomputable def sixLabelledDiracComm
    (label : Fin 6 → Fin 4) (D : SixMat) (f : Fin 4 → ℂ) :
    SixH →L[ℂ] SixH :=
  (D * Matrix.diagonal (fun i => f (label i)) -
    Matrix.diagonal (fun i => f (label i)) * D
    ).toEuclideanLin.toContinuousLinearMap

/-- The two-bit Hamming sum witness is the sum of both truth bits. -/
theorem sixTruthSum_eq_bits (v : Fin 4) :
    twoBitOppositeCornerSum v =
      squareTruthBitP v + squareTruthBitQ v := by
  fin_cases v <;>
    norm_num [twoBitOppositeCornerSum, squareTruthBitP, squareTruthBitQ]

/-- The 01-to-10 witness differs from Q-P by a scalar constant. -/
theorem sixTruthDifference_eq_bits (v : Fin 4) :
    twoBitOppositeCornerDifference v =
      1 - squareTruthBitP v + squareTruthBitQ v := by
  fin_cases v <;>
    norm_num [twoBitOppositeCornerDifference, squareTruthBitP, squareTruthBitQ]

/-- The actual first and second labelled coordinate commutators
sum to i times the commutator of the distance-to-00 witness. -/
theorem sixLabelled_sumWitness_matrix
    (label : Fin 6 → Fin 4) (D : SixMat) :
    labelledSquareA label D + labelledSquareB label D =
      Complex.I •
      (D * Matrix.diagonal
         (fun i => twoBitOppositeCornerSum (label i)) -
       Matrix.diagonal
         (fun i => twoBitOppositeCornerSum (label i)) * D) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply,
    labelledSquareA, labelledSquareB, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]
  rw [sixTruthSum_eq_bits, sixTruthSum_eq_bits]
  ring

/-- The difference witness gives the opposite signed coordinate
difference, with an irrelevant constant shift. -/
theorem sixLabelled_differenceWitness_matrix
    (label : Fin 6 → Fin 4) (D : SixMat) :
    labelledSquareB label D - labelledSquareA label D =
      Complex.I •
      (D * Matrix.diagonal
         (fun i => twoBitOppositeCornerDifference (label i)) -
       Matrix.diagonal
         (fun i => twoBitOppositeCornerDifference (label i)) * D) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply,
    labelledSquareA, labelledSquareB,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]
  rw [sixTruthDifference_eq_bits, sixTruthDifference_eq_bits]
  ring

/-- Multiplying an actual six-dimensional Hilbert operator by i
preserves its norm exactly. -/
theorem sixLabelled_imaginaryOperator_norm
    (M : SixMat) :
    ‖(Complex.I • M).toEuclideanLin.toContinuousLinearMap‖ =
      ‖M.toEuclideanLin.toContinuousLinearMap‖ := by
  have hs :
      (Complex.I • M).toEuclideanLin.toContinuousLinearMap =
        Complex.I • M.toEuclideanLin.toContinuousLinearMap := by
    ext v
    simp
  rw [hs, norm_smul]
  simp

/-- Admissibility of both opposite-corner Hamming witnesses yields
simultaneous genuine sum and difference contractions of the actual
labelled six-dimensional coordinate operators. -/
theorem sixLabelled_oppositeWitnesses_contractions
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsum : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerSum‖ ≤ 1)
    (hdiff : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerDifference‖ ≤ 1) :
    ‖sixLabelledAOperator label D +
      sixLabelledBOperator label D‖ ≤ 1 ∧
    ‖sixLabelledAOperator label D -
      sixLabelledBOperator label D‖ ≤ 1 := by
  have hp :
      ‖(labelledSquareA label D + labelledSquareB label D
        ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
    rw [sixLabelled_sumWitness_matrix,
      sixLabelled_imaginaryOperator_norm]
    exact hsum
  have hm :
      ‖(labelledSquareB label D - labelledSquareA label D
        ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
    rw [sixLabelled_differenceWitness_matrix,
      sixLabelled_imaginaryOperator_norm]
    exact hdiff
  have happ :
      (labelledSquareA label D + labelledSquareB label D
        ).toEuclideanLin.toContinuousLinearMap =
      sixLabelledAOperator label D + sixLabelledBOperator label D := by
    ext v
    simp [sixLabelledAOperator, sixLabelledBOperator]
  have hsub :
      (labelledSquareB label D - labelledSquareA label D
        ).toEuclideanLin.toContinuousLinearMap =
      sixLabelledBOperator label D - sixLabelledAOperator label D := by
    ext v
    simp [sixLabelledAOperator, sixLabelledBOperator]
  rw [happ] at hp
  rw [hsub] at hm
  exact ⟨hp, by simpa only [norm_sub_rev] using hm⟩

/-- Homogeneity of the six-dimensional represented Dirac
commutator under complex rescaling of every truth value. -/
theorem sixLabelledDiracComm_smul
    (label : Fin 6 → Fin 4) (D : SixMat)
    (f : Fin 4 → ℂ) (t : ℂ) :
    sixLabelledDiracComm label D (fun i => t * f i) =
      t • sixLabelledDiracComm label D f := by
  have hmatrix :
      D * Matrix.diagonal (fun i => t * f (label i)) -
          Matrix.diagonal (fun i => t * f (label i)) * D =
      t • (D * Matrix.diagonal (fun i => f (label i)) -
          Matrix.diagonal (fun i => f (label i)) * D) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    ring
  unfold sixLabelledDiracComm
  rw [hmatrix]
  ext v
  simp

/-- The 00-to-01 dual unit-edge bound makes the first true
Hermitian coordinate commutator have norm at least one. -/
theorem sixLabelled_firstCoordinate_norm_ge_one
    (label : Fin 6 → Fin 4) (D : SixMat)
    (h01 : ∀ f : Fin 4 → ℂ,
      ‖sixLabelledDiracComm label D f‖ ≤ 1 →
        ‖f 0 - f 1‖ ≤ 1) :
    1 ≤ ‖sixLabelledAOperator label D‖ := by
  have hnorm : ‖sixLabelledAOperator label D‖ =
      ‖sixLabelledDiracComm label D squareTruthBitP‖ := by
    unfold sixLabelledAOperator sixLabelledDiracComm
    rw [labelledSquareA_eq_diagonal_commutator,
      sixLabelled_imaginaryOperator_norm]
    rfl
  apply complexUnitBallDual_norm_ge_one
  intro t ht
  let f : Fin 4 → ℂ := fun v => t * squareTruthBitP v
  have hscale :
      ‖sixLabelledDiracComm label D f‖ =
        ‖t • sixLabelledAOperator label D‖ := by
    change ‖sixLabelledDiracComm label D
      (fun v => t * squareTruthBitP v)‖ = _
    rw [sixLabelledDiracComm_smul]
    simp only [norm_smul, ← hnorm]
  have hv : ‖f 0 - f 1‖ ≤ 1 :=
    h01 f (by rw [hscale]; exact ht)
  simpa [f, squareTruthBitP] using hv

/-- The second dual edge bound likewise makes the second
Hermitian coordinate commutator have norm at least one. -/
theorem sixLabelled_secondCoordinate_norm_ge_one
    (label : Fin 6 → Fin 4) (D : SixMat)
    (h02 : ∀ f : Fin 4 → ℂ,
      ‖sixLabelledDiracComm label D f‖ ≤ 1 →
        ‖f 0 - f 2‖ ≤ 1) :
    1 ≤ ‖sixLabelledBOperator label D‖ := by
  have hnorm : ‖sixLabelledBOperator label D‖ =
      ‖sixLabelledDiracComm label D squareTruthBitQ‖ := by
    unfold sixLabelledBOperator sixLabelledDiracComm
    rw [labelledSquareB_eq_diagonal_commutator,
      sixLabelled_imaginaryOperator_norm]
    rfl
  apply complexUnitBallDual_norm_ge_one
  intro t ht
  let f : Fin 4 → ℂ := fun v => t * squareTruthBitQ v
  have hscale :
      ‖sixLabelledDiracComm label D f‖ =
        ‖t • sixLabelledBOperator label D‖ := by
    change ‖sixLabelledDiracComm label D
      (fun v => t * squareTruthBitQ v)‖ = _
    rw [sixLabelledDiracComm_smul]
    simp only [norm_smul, ← hnorm]
  have hv : ‖f 0 - f 2‖ ≤ 1 :=
    h02 f (by rw [hscale]; exact ht)
  simpa [f, squareTruthBitQ] using hv

/-- Dual unit-edge bounds and the two opposite-corner witnessed
commutator contractions produce both exact coordinate norms. -/
theorem sixLabelled_oppositeWitnesses_normOne
    (label : Fin 6 → Fin 4) (D : SixMat)
    (h01 : ∀ f : Fin 4 → ℂ,
      ‖sixLabelledDiracComm label D f‖ ≤ 1 → ‖f 0 - f 1‖ ≤ 1)
    (h02 : ∀ f : Fin 4 → ℂ,
      ‖sixLabelledDiracComm label D f‖ ≤ 1 → ‖f 0 - f 2‖ ≤ 1)
    (hsum : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerSum‖ ≤ 1)
    (hdiff : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerDifference‖ ≤ 1) :
    ‖sixLabelledAOperator label D‖ = 1 ∧
    ‖sixLabelledBOperator label D‖ = 1 := by
  obtain ⟨hp, hm⟩ :=
    sixLabelled_oppositeWitnesses_contractions label D hsum hdiff
  obtain ⟨ha, hb⟩ := twoDirection_norms_le_one
    (sixLabelledAOperator label D) (sixLabelledBOperator label D) hp hm
  exact ⟨le_antisymm ha (sixLabelled_firstCoordinate_norm_ge_one label D h01),
    le_antisymm hb (sixLabelled_secondCoordinate_norm_ge_one label D h02)⟩

/-- The six-dimensional labelled Connes dual metric quantifies over
all complex four-truth observables with the actual Dirac unit ball. -/
def sixLabelledAdmissible (label : Fin 6 → Fin 4) (D : SixMat) : Type :=
  { f : Fin 4 → ℂ // ‖sixLabelledDiracComm label D f‖ ≤ 1 }

noncomputable def sixLabelledConnesDistance
    (label : Fin 6 → Fin 4) (D : SixMat) (u v : Fin 4) : ℝ≥0∞ :=
  ⨆ f : sixLabelledAdmissible label D,
    (‖f.val u - f.val v‖₊ : ℝ≥0∞)

/-- A finite labelled Connes dual distance bounds every
admissible complex truth observable's endpoint difference. -/
theorem sixLabelledConnesDistance_bounds
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4) (r : ℝ≥0)
    (hd : sixLabelledConnesDistance label D u v ≤ (r : ℝ≥0∞))
    (f : Fin 4 → ℂ)
    (hf : ‖sixLabelledDiracComm label D f‖ ≤ 1) :
    ‖f u - f v‖ ≤ (r : ℝ) := by
  have hle :
      (‖f u - f v‖₊ : ℝ≥0∞) ≤
        sixLabelledConnesDistance label D u v := by
    unfold sixLabelledConnesDistance
    exact le_iSup
      (fun g : sixLabelledAdmissible label D =>
        (‖g.val u - g.val v‖₊ : ℝ≥0∞))
      (⟨f, hf⟩ : sixLabelledAdmissible label D)
  have hnn : ‖f u - f v‖₊ ≤ r :=
    ENNReal.coe_le_coe.mp (hle.trans hd)
  have hreal : (‖f u - f v‖₊ : ℝ) ≤ (r : ℝ) :=
    NNReal.coe_le_coe.mpr hnn
  simpa only [coe_nnnorm] using hreal

/-- The four-truth metric's two adjacent exact unit distances and
both explicit opposite-corner witnesses construct the genuine
six-dimensional Hilbert extremal system, with no postulated signed
eigenvectors, and with a common residual of complex dimension two. -/
theorem sixLabelled_exactEdges_witnessed_extremalSystem
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hd01 : sixLabelledConnesDistance label D 0 1 = 1)
    (hd02 : sixLabelledConnesDistance label D 0 2 = 1)
    (hsum : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerSum‖ ≤ 1)
    (hdiff : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerDifference‖ ≤ 1) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus) ∧
      S.A = sixLabelledAOperator label D ∧
      S.B = sixLabelledBOperator label D := by
  have h01 : ∀ f : Fin 4 → ℂ,
      ‖sixLabelledDiracComm label D f‖ ≤ 1 →
      ‖f 0 - f 1‖ ≤ 1 := by
    intro f hf
    exact sixLabelledConnesDistance_bounds
      label D 0 1 1 (by simp [hd01]) f hf
  have h02 : ∀ f : Fin 4 → ℂ,
      ‖sixLabelledDiracComm label D f‖ ≤ 1 →
      ‖f 0 - f 2‖ ≤ 1 := by
    intro f hf
    exact sixLabelledConnesDistance_bounds
      label D 0 2 1 (by simp [hd02]) f hf
  obtain ⟨hnA, hnB⟩ :=
    sixLabelled_oppositeWitnesses_normOne label D h01 h02 hsum hdiff
  obtain ⟨hplus, hminus⟩ :=
    sixLabelled_oppositeWitnesses_contractions label D hsum hdiff
  exact sixLabelledSquare_exists_extremalSystem
    label D hD hplus hminus hnA hnB

end Neoplatonic.LTR
