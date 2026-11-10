import Neoplatonic.LTR.SixDimensionalLabelledAttainment
import Neoplatonic.LTR.SixDimensionalLabelledPauliBridge
import Mathlib.Tactic

/-!
# LTR-MAN-77: exact six-dimensional Hamming distances force witnesses

MAN-77 proves compact attainment of the two opposite-corner
distance-two Connes dual suprema in any labelled six-dimensional
diagonal truth representation.

After phase and translation normalization, the four exact unit
edge distances force the intermediate complex truth values at 01
and 10 to be one. The recovered attainers are exactly the two
canonical opposite-corner Hamming observables from MAN-27.
Their true Dirac commutators are therefore contractions.

Combining this with MAN-76 constructs the real signed orthonormal
eigenquartet and the actual two-dimensional Pauli residual directly
from all six exact Connes distances. Under the separate no-opposite
Dirac-coupling condition, MAN-74/75/76 give Pauli vector orthogonality
without further witness or eigenvector assumptions.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- All six exact Hamming dual distances force the two canonical
opposite-corner observables to be admissible for the actual six-
dimensional Dirac operator, without assuming attainment. -/
theorem sixLabelled_exactHamming_force_witnesses
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hd01 : sixLabelledConnesDistance label D 0 1 = 1)
    (hd02 : sixLabelledConnesDistance label D 0 2 = 1)
    (hd31 : sixLabelledConnesDistance label D 3 1 = 1)
    (hd32 : sixLabelledConnesDistance label D 3 2 = 1)
    (hd03 : sixLabelledConnesDistance label D 0 3 = 2)
    (hd12 : sixLabelledConnesDistance label D 1 2 = 2) :
    ‖sixLabelledDiracComm label D
      twoBitOppositeCornerSum‖ ≤ 1 ∧
    ‖sixLabelledDiracComm label D
      twoBitOppositeCornerDifference‖ ≤ 1 := by
  let L : (Fin 4 → ℂ) → ℝ :=
    fun f => ‖sixLabelledDiracComm label D f‖
  have hupper : ∀ f : Fin 4 → ℂ, L f ≤ 1 →
      ‖f 0 - f 1‖ ≤ 1 ∧ ‖f 0 - f 2‖ ≤ 1 ∧
      ‖f 3 - f 1‖ ≤ 1 ∧ ‖f 3 - f 2‖ ≤ 1 := by
    intro f hf
    have h01 := sixLabelledConnesDistance_bounds
      label D 0 1 1 (by simp [hd01]) f hf
    have h02 := sixLabelledConnesDistance_bounds
      label D 0 2 1 (by simp [hd02]) f hf
    have h31 := sixLabelledConnesDistance_bounds
      label D 3 1 1 (by simp [hd31]) f hf
    have h32 := sixLabelledConnesDistance_bounds
      label D 3 2 1 (by simp [hd32]) f hf
    exact ⟨h01, h02, h31, h32⟩
  have hsum : ∃ f : Fin 4 → ℂ,
      L f ≤ 1 ∧ f 0 = 0 ∧ f 3 = 2 := by
    have hatt : ∃ f : sixLabelledAdmissible label D,
        ‖f.val 3 - f.val 0‖ = 2 :=
      sixLabelled_distanceTwo_attained label D
        hd01 hd02 hd03 0 3 hd03
    obtain ⟨g, hgunit, hg0, hg3⟩ :=
      sixLabelled_normalizeSubtypeAttainer label D 0 3 hatt
    exact ⟨g, hgunit, hg0, hg3⟩
  have hdiff : ∃ f : Fin 4 → ℂ,
      L f ≤ 1 ∧ f 1 = 0 ∧ f 2 = 2 := by
    have hatt : ∃ f : sixLabelledAdmissible label D,
        ‖f.val 2 - f.val 1‖ = 2 :=
      sixLabelled_distanceTwo_attained label D
        hd01 hd02 hd03 1 2 hd12
    obtain ⟨g, hgunit, hg1, hg2⟩ :=
      sixLabelled_normalizeSubtypeAttainer label D 1 2 hatt
    exact ⟨g, hgunit, hg1, hg2⟩
  exact twoBitOppositeAttainers_force_coordinateWitnesses
    L hupper hsum hdiff

/-- Exact Hamming metric values generate a concrete six-dimensional
extremal spectral system, signed orthonormal quartet, and residual
complex dimension two without postulating any witness functions. -/
theorem sixLabelled_exactHamming_exists_extremalSystem
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hd01 : sixLabelledConnesDistance label D 0 1 = 1)
    (hd02 : sixLabelledConnesDistance label D 0 2 = 1)
    (hd31 : sixLabelledConnesDistance label D 3 1 = 1)
    (hd32 : sixLabelledConnesDistance label D 3 2 = 1)
    (hd03 : sixLabelledConnesDistance label D 0 3 = 2)
    (hd12 : sixLabelledConnesDistance label D 1 2 = 2) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus) ∧
      S.A = sixLabelledAOperator label D ∧
      S.B = sixLabelledBOperator label D := by
  obtain ⟨hsum, hdiff⟩ :=
    sixLabelled_exactHamming_force_witnesses
      label D hd01 hd02 hd31 hd32 hd03 hd12
  exact sixLabelled_exactEdges_witnessed_extremalSystem
    label D hD hd01 hd02 hsum hdiff

/-- The necessary residual Pauli orthogonality result now follows
from exact Hamming distances and no-opposite-corner Dirac support,
without separate attainment, witness, or quartet hypotheses. -/
theorem sixLabelled_exactHamming_noOpposite_pauliOrthogonal
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hd01 : sixLabelledConnesDistance label D 0 1 = 1)
    (hd02 : sixLabelledConnesDistance label D 0 2 = 1)
    (hd31 : sixLabelledConnesDistance label D 3 1 = 1)
    (hd32 : sixLabelledConnesDistance label D 3 2 = 1)
    (hd03 : sixLabelledConnesDistance label D 0 3 = 2)
    (hd12 : sixLabelledConnesDistance label D 1 2 = 2)
    (hopp : ∀ i j : Fin 6,
      squareTruthOpposite (label i) (label j) → D i j = 0) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        pauliRealDot (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp)) = 0 := by
  obtain ⟨hsum, hdiff⟩ :=
    sixLabelled_exactHamming_force_witnesses
      label D hd01 hd02 hd31 hd32 hd03 hd12
  exact sixLabelled_witnessed_noOpposite_pauliOrthogonal
    label D hD hd01 hd02 hsum hdiff hopp

/-- Universal exact two-bit Hamming distances supply the six
explicit opposite-corner Dirac witness norms, with arbitrary
faithful six-dimensional truth labels. -/
theorem sixLabelled_fullHamming_force_witnesses
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    ‖sixLabelledDiracComm label D
      twoBitOppositeCornerSum‖ ≤ 1 ∧
    ‖sixLabelledDiracComm label D
      twoBitOppositeCornerDifference‖ ≤ 1 := by
  apply sixLabelled_exactHamming_force_witnesses label D
  · simpa [twoBitSquareHamming] using hham 0 1
  · simpa [twoBitSquareHamming] using hham 0 2
  · simpa [twoBitSquareHamming] using hham 3 1
  · simpa [twoBitSquareHamming] using hham 3 2
  · simpa [twoBitSquareHamming] using hham 0 3
  · simpa [twoBitSquareHamming] using hham 1 2

end Neoplatonic.LTR
