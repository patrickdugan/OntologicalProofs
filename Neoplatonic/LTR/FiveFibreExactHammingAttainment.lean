import Neoplatonic.LTR.FiveFibreCompactAttainment
import Neoplatonic.LTR.FiveFibreDiracContinuity
import Mathlib.Tactic

/-!
# LTR-MAN-35: remove the distance-attainment hypothesis

MAN-33 proves that normalized admissible observables form a compact
set when the Connes dual distances from 00 are finite. Its maximum
attains every prescribed finite distance, conditional only on
continuity of the genuine commutator norm.

MAN-34 proves that continuity by constructing a finite-dimensional
complex-linear map into bounded Hilbert operators.

Together these results show that all exact two-bit Hamming distances
force the two opposite-corner extrema to be attained by genuine
complex-valued admissible observables. MAN-32 then forces the explicit
coordinate witnesses and unit coordinate commutator norms.

The final conditional obstruction here assumes only the actual
two ordered coordinate products vanish and D is Hermitian. Producing
those products from MAN-21 and the literal coordinate grading is
the next spectral integration obligation.
-/

namespace Neoplatonic.LTR

/-- Exact finite complex Connes distance two is attained by an actual
observable in the canonical faithful five-dimensional representation. -/
theorem fiveFibreSquare_distanceTwo_attained
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hd01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (hd02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hd03 : fiveFibreSquareConnesDualDistance D 0 3 = 2)
    (u v : Fin 4)
    (hduv : fiveFibreSquareConnesDualDistance D
      u.castSucc v.castSucc = 2) :
    ∃ f : fiveFibreSquareAdmissible D,
      ‖f.val v.castSucc - f.val u.castSucc‖ = 2 :=
  fiveFibreSquare_distanceTwo_attained_of_continuous
    D hd01 hd02 hd03 u v hduv
    (fiveFibreSquareDiracFourNorm_continuous D)

/-- All six exact Hamming dual distances force the two actual
canonical unit Dirac-commutator witnesses. -/
theorem fiveFibreSquare_exactHamming_force_witnesses
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hd01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (hd02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hd31 : fiveFibreSquareConnesDualDistance D 3 1 = 1)
    (hd32 : fiveFibreSquareConnesDualDistance D 3 2 = 1)
    (hd03 : fiveFibreSquareConnesDualDistance D 0 3 = 2)
    (hd12 : fiveFibreSquareConnesDualDistance D 1 2 = 2) :
    ‖fiveFibreSquareDiracComm D
      (fiveFibreSquareLift twoBitOppositeCornerSum)‖ ≤ 1 ∧
    ‖fiveFibreSquareDiracComm D
      (fiveFibreSquareLift twoBitOppositeCornerDifference)‖ ≤ 1 := by
  have hatt03 : ∃ f : fiveFibreSquareAdmissible D,
      ‖f.val 3 - f.val 0‖ = 2 := by
    simpa using fiveFibreSquare_distanceTwo_attained
      D hd01 hd02 hd03 (0 : Fin 4) (3 : Fin 4)
      (by simpa using hd03)
  have hatt12 : ∃ f : fiveFibreSquareAdmissible D,
      ‖f.val 2 - f.val 1‖ = 2 := by
    simpa using fiveFibreSquare_distanceTwo_attained
      D hd01 hd02 hd03 (1 : Fin 4) (2 : Fin 4)
      (by simpa using hd12)
  exact fiveFibreSquare_attainedOpposites_force_witnesses
    D hd01 hd02 hd31 hd32 hatt03 hatt12

/-- The six exact Hamming Connes distances force the first and
second Hermitian coordinate commutators to have norm exactly one. -/
theorem fiveFibreSquare_exactHamming_normOne
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hd01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (hd02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hd31 : fiveFibreSquareConnesDualDistance D 3 1 = 1)
    (hd32 : fiveFibreSquareConnesDualDistance D 3 2 = 1)
    (hd03 : fiveFibreSquareConnesDualDistance D 0 3 = 2)
    (hd12 : fiveFibreSquareConnesDualDistance D 1 2 = 2) :
    ‖(fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap‖ = 1 ∧
    ‖(fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap‖ = 1 := by
  obtain ⟨hsum, hdiff⟩ :=
    fiveFibreSquare_exactHamming_force_witnesses
      D hd01 hd02 hd31 hd32 hd03 hd12
  exact fiveFibreSquare_exactEdgeDistance_normOne
    D hd01 hd02 hsum hdiff

/-- Conditional canonical 5D no-go with all metric and eigenvector
attainment hypotheses eliminated. Only the two matrix zero products
remain as the separate spectral algebraic obligation. -/
theorem fiveFibreSquare_exactHamming_noGo_of_zeroProducts
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0)
    (hd01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (hd02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hd31 : fiveFibreSquareConnesDualDistance D 3 1 = 1)
    (hd32 : fiveFibreSquareConnesDualDistance D 3 2 = 1)
    (hd03 : fiveFibreSquareConnesDualDistance D 0 3 = 2)
    (hd12 : fiveFibreSquareConnesDualDistance D 1 2 = 2) :
    False := by
  obtain ⟨hAnorm, hBnorm⟩ :=
    fiveFibreSquare_exactHamming_normOne
      D hd01 hd02 hd31 hd32 hd03 hd12
  have hAne : fiveFibreSquareA D ≠ 0 := by
    intro hz
    have hzNorm :
        ‖(fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap‖ = 0 := by
      simp [hz]
    linarith
  have hBne : fiveFibreSquareB D ≠ 0 := by
    intro hz
    have hzNorm :
        ‖(fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap‖ = 0 := by
      simp [hz]
    linarith
  exact fiveFibreSquare_exactOppositeDistance_noGo
    D hD hAB hBA hAne hBne hd03

end Neoplatonic.LTR
