import Neoplatonic.LTR.SixDimensionalAmbientSignedInvolution
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-91: exact Hamming Dirac saturation makes an ambient matrix involution

MAN-89 constructs the true 2x2 residual signed witness matrix with
square equal to identity at either saturated opposite-corner energy
pattern. MAN-90 transports this to the compressed residual bounded
Hilbert operator. MAN-91 then supplies the full ambient six-dimensional
square-one identity by adjoining the orthonormal signed quartet.

This module instantiates the chain from one actual Hermitian
six-dimensional labelled Dirac matrix and six exact Hamming Connes
distances. It also transports the resulting bounded Hilbert operator
identity back to the original 6x6 complex matrix of the witness.

For 00--11 survival, W+=i[D,P+Q] squares to I6.
For 01--10 survival, W-=i[D,P-Q] squares to I6.
No external eigenvector hypotheses are imposed.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A genuine Euclidean 6x6 complex matrix is an involution
whenever its corresponding bounded complex Hilbert operator is. -/
theorem sixMatrix_involution_of_trueHilbert_involution
    (W : SixMat)
    (h : W.toEuclideanLin.toContinuousLinearMap *
      W.toEuclideanLin.toContinuousLinearMap = 1) :
    W * W = 1 := by
  let F := Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)
  have h' : F W * F W = 1 := by
    change W.toEuclideanLin.toContinuousLinearMap *
      W.toEuclideanLin.toContinuousLinearMap = 1
    exact h
  have hm : F (W * W) = F W * F W := map_mul F W W
  have hone : F (1 : SixMat) = 1 := map_one F
  apply F.injective
  rw [hm, hone]
  exact h'

/-- The actual 00--11 saturated Hermitian Dirac witness A+B
is an involution on the entire six-dimensional complex Hilbert
space, including its four extremal and two residual dimensions. -/
theorem sixLabelled_exactHamming_saturated03_ambientPlus_involution
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    (sixLabelledAOperator label D + sixLabelledBOperator label D) *
      (sixLabelledAOperator label D + sixLabelledBOperator label D) = 1 := by
  obtain ⟨S, hq, hA, hB, hmat, _⟩ :=
    sixLabelled_exactHamming_saturated03_residualPlus_involution
      label D hD hham h03 h12
  have hr := S.residualPlus_involution_of_pauli hq hmat
  have hamb := S.ambientPlus_involution_of_residual hr
  simpa only [hA, hB] using hamb

/-- The actual 01--10 saturated Hermitian Dirac witness A-B
is an involution on the entire six-dimensional Hilbert space. -/
theorem sixLabelled_exactHamming_saturated12_ambientMinus_involution
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    (sixLabelledAOperator label D - sixLabelledBOperator label D) *
      (sixLabelledAOperator label D - sixLabelledBOperator label D) = 1 := by
  obtain ⟨S, hq, hA, hB, hmat, _⟩ :=
    sixLabelled_exactHamming_saturated12_residualMinus_involution
      label D hD hham h03 h12
  have hr := S.residualMinus_involution_of_pauli hq hmat
  have hamb := S.ambientMinus_involution_of_residual hr
  simpa only [hA, hB] using hamb

/-- This is the same exact saturated 00--11 involution stated on
the original true complex 6x6 Dirac coordinate-commutator matrices. -/
theorem sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    (labelledSquareA label D + labelledSquareB label D) *
      (labelledSquareA label D + labelledSquareB label D) = 1 := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  have hmap : W.toEuclideanLin.toContinuousLinearMap =
      sixLabelledAOperator label D + sixLabelledBOperator label D := by
    change (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) W =
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareA label D) +
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareB label D)
    exact map_add (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) _ _
  apply sixMatrix_involution_of_trueHilbert_involution W
  rw [hmap]
  exact sixLabelled_exactHamming_saturated03_ambientPlus_involution
    label D hD hham h03 h12

/-- Original 6x6 Dirac matrix identity in the 01--10 saturated
case: the difference of the imaginary coordinate commutators
squares to the identity matrix. -/
theorem sixLabelled_exactHamming_saturated12_trueMatrixMinus_involution
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    (labelledSquareA label D - labelledSquareB label D) *
      (labelledSquareA label D - labelledSquareB label D) = 1 := by
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  have hmap : W.toEuclideanLin.toContinuousLinearMap =
      sixLabelledAOperator label D - sixLabelledBOperator label D := by
    change (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) W =
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareA label D) -
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareB label D)
    exact map_sub (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) _ _
  apply sixMatrix_involution_of_trueHilbert_involution W
  rw [hmap]
  exact sixLabelled_exactHamming_saturated12_ambientMinus_involution
    label D hD hham h03 h12

end Neoplatonic.LTR
