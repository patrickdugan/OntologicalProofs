import Neoplatonic.LTR.FiveFibreIsolatedVertex
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# LTR-MAN-25: direct Hamming dual contradiction from the isolated fibre

MAN-24 proves the 11 atomic truth indicator commutes with a five-by-five
Hermitian Dirac matrix once the coordinate commutators are nonzero and
have vanishing ordered products. Scale that indicator to value 3 on
truth vertex 11 and 0 on the other truth vertices.

The genuine finite matrix commutator of this real observable is zero,
so its continuous Hilbert-space operator commutator has norm zero.
The Connes dual upper-bound requirement at the opposite corners 00 and
11 would bound the value difference by 2, whereas this admissible
observable has difference 3. This closes the metric contradiction for
the canonical 5D multiplicity pattern (2,1,1,1), assuming the spectral
zero-product hypotheses already isolated in MAN-21.

The other doubled-vertex patterns and derivation of MAN-21's operator
hypotheses from exact metric witnesses remain to be formalized.
-/

namespace Neoplatonic.LTR

/-- Coordinate entries agree with the literal imaginary commutator
i[D, P] for the diagonal first-truth-coordinate projection. -/
theorem fiveFibreSquareA_eq_diagonal_commutator
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    fiveFibreSquareA D =
      Complex.I • (D * Matrix.diagonal fiveFibreSquareP -
        Matrix.diagonal fiveFibreSquareP * D) := by
  ext i j
  simp [fiveFibreSquareA, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Coordinate entries agree with i[D, Q] for the other Boolean bit. -/
theorem fiveFibreSquareB_eq_diagonal_commutator
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    fiveFibreSquareB D =
      Complex.I • (D * Matrix.diagonal fiveFibreSquareQ -
        Matrix.diagonal fiveFibreSquareQ * D) := by
  ext i j
  simp [fiveFibreSquareB, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A separating Hamming-violating observable is allowed by the
commutator constraint once the 11 sector is isolated. -/
theorem fiveFibreSquare_scaledVertex11_commutes
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (h03 : D 0 3 = 0) (h43 : D 4 3 = 0)
    (h13 : D 1 3 = 0) (h23 : D 2 3 = 0) :
    D * Matrix.diagonal
      (fun i : Fin 5 => if i = 3 then (3 : ℂ) else 0) =
    Matrix.diagonal
      (fun i : Fin 5 => if i = 3 then (3 : ℂ) else 0) * D := by
  have h30 : D 3 0 = 0 := by simpa [h03] using hD 3 0
  have h34 : D 3 4 = 0 := by simpa [h43] using hD 3 4
  have h31 : D 3 1 = 0 := by simpa [h13] using hD 3 1
  have h32 : D 3 2 = 0 := by simpa [h23] using hD 3 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul,
      h03, h43, h13, h23, h30, h34, h31, h32]

/-- Canonical five-dimensional spectral obstruction against the
explicit Connes-dual Hamming upper bound d(00,11) ≤ 2.

The dual hypothesis quantifies over all observables constant on the
duplicate 00 fibre, with the actual complex Hilbert operator norm of
their Dirac commutator. All other hypotheses are matrix-identities
checked in earlier LTR-MAN steps. -/
theorem fiveFibreSquare_connesDual_hamming_noGo
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0)
    (hA : fiveFibreSquareA D ≠ 0)
    (hB : fiveFibreSquareB D ≠ 0)
    (hdual :
      ∀ f : Fin 5 → ℂ, f 4 = f 0 →
        ‖(D * Matrix.diagonal f -
          Matrix.diagonal f * D).toEuclideanLin‖ ≤ 1 →
        ‖f 0 - f 3‖ ≤ (2 : ℝ)) :
    False := by
  obtain ⟨h03, h43, h13, h23⟩ :=
    fiveFibreSquare_vertex11_isolated D hD hAB hBA hA hB
  let f : Fin 5 → ℂ := fun i => if i = 3 then (3 : ℂ) else 0
  have hf : f 4 = f 0 := by norm_num [f]
  have hcomm : D * Matrix.diagonal f = Matrix.diagonal f * D :=
    fiveFibreSquare_scaledVertex11_commutes D hD h03 h43 h13 h23
  have hz : D * Matrix.diagonal f - Matrix.diagonal f * D = 0 :=
    sub_eq_zero.mpr hcomm
  have hunit :
      ‖(D * Matrix.diagonal f -
        Matrix.diagonal f * D).toEuclideanLin‖ ≤ 1 := by
    rw [hz]
    simp
  have hbound := hdual f hf hunit
  norm_num [f] at hbound

end Neoplatonic.LTR
