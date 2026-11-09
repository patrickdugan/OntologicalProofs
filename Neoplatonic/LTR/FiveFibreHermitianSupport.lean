import Neoplatonic.LTR.FiveFibreSquareProducts
import Neoplatonic.LTR.TwoBitSquareSupport
import Mathlib.Tactic

/-!
# LTR-MAN-23: support consequences of five-dimensional zero products

The MAN-22 exact entries are now combined with Hermiticity of the Dirac
matrix. From the two zero products A B = B A = 0, every opposite-corner
Dirac coupling vanishes, including the coupling from the doubled fibre.

Moreover, if the 01--11 edge is nonzero, the two incident 00--01
couplings and the 10--11 edge must vanish. Similarly, nonzero
10--11 forces both 00--10 couplings and the 01--11 edge to vanish.
This proves the local branch exclusions on the actual matrix entries,
with all three singleton vertex fibres accounted for.

No spectral or metric assumptions beyond the two zero products enter
this lemma. The degree and Connes-distance contradiction is next.
-/

namespace Neoplatonic.LTR

/-- Hermiticity and the zero coordinate products remove the direct
distance-two Dirac edges 00--11 (both copies of 00) and 01--10. -/
theorem fiveFibreSquare_oppositeCouplings_zero
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0) :
    D 0 3 = 0 ∧ D 4 3 = 0 ∧ D 1 2 = 0 := by
  obtain ⟨h03, h43, h12, -, -, -, -, -⟩ :=
    fiveFibreSquare_product_zero_entries D hAB hBA
  refine ⟨?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp h03 with h | h
    · exact h
    · simpa [h] using hD 0 3
  · rcases mul_eq_zero.mp h43 with h | h
    · exact h
    · simpa [h] using hD 4 3
  · rcases mul_eq_zero.mp h12 with h | h
    · exact h
    · simpa [h] using hD 1 2

/-- Actual one-dimensional-fibre branch exclusions. The 01 and 10
vertices are singleton fibres, so products along paths through them
cannot cancel against a second intermediate coordinate. The 11
vertex is also a singleton fibre, giving the last exclusion. -/
theorem fiveFibreSquare_singletonBranches
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0) :
    (D 1 3 ≠ 0 → D 0 1 = 0 ∧ D 4 1 = 0 ∧ D 2 3 = 0) ∧
    (D 2 3 ≠ 0 → D 0 2 = 0 ∧ D 4 2 = 0 ∧ D 1 3 = 0) := by
  obtain ⟨_, _, _, h01, h41, h02, h42, h13_32⟩ :=
    fiveFibreSquare_product_zero_entries D hAB hBA
  constructor
  · intro hc
    have h32 : D 3 2 = 0 :=
      (mul_eq_zero.mp h13_32).resolve_left hc
    have hd : D 2 3 = 0 := by simpa [h32] using hD 2 3
    exact ⟨(mul_eq_zero.mp h01).resolve_right hc,
      (mul_eq_zero.mp h41).resolve_right hc, hd⟩
  · intro hd
    have h32ne : D 3 2 ≠ 0 := by
      intro h32
      have h23 : D 2 3 = 0 := by simpa [h32] using hD 2 3
      exact hd h23
    exact ⟨(mul_eq_zero.mp h02).resolve_right hd,
      (mul_eq_zero.mp h42).resolve_right hd,
      (mul_eq_zero.mp h13_32).resolve_right h32ne⟩

end Neoplatonic.LTR
