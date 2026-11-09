import Neoplatonic.LTR.ScalarFibreNonzeroComposition
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-17: a five-dimensional spectral residual matrix certificate

This is the finite matrix normal-form step in the proposed Hamming-square
five-dimensional obstruction.

Suppose an orthonormal basis of the five-dimensional complex Hilbert space
begins with one +1 and one -1 eigenvector for A, followed by one +1 and
one -1 eigenvector for B. The MAN-13 annihilation theorem gives the
cross-direction zero columns. Self-adjointness gives the matching zero rows.

A and B can then act only on a common residual line, besides their
respective extremal eigenvectors. The paired eigenvalues cancel in the trace,
and tracelessness forces the residual diagonal entries to vanish. Thus
A B = B A = 0.

The theorem below certifies the concrete five-by-five matrix consequence,
using Hermitian entry symmetry and all four extremal eigenvector columns.
Constructing this joint orthonormal basis from the finite-dimensional
Hilbert eigenspaces, and connecting the resulting product to the four
atomic truth fibres, are separate formalization obligations.
-/

namespace Neoplatonic.LTR

private def fiveDimAWeight (i : Fin 5) : ℂ :=
  if i = 0 then 1 else if i = 1 then -1 else 0

private def fiveDimBWeight (i : Fin 5) : ℂ :=
  if i = 2 then 1 else if i = 3 then -1 else 0

/-- On a five-dimensional joint extremal eigenbasis, self-adjoint
traceless coordinate operators have disjoint diagonal supports.

Columns 0 and 1 are A-eigenvectors at +1 and -1; columns 2 and 3
are B-eigenvectors at +1 and -1. The opposite operator annihilates
each pair. Hermitian symmetry eliminates the off-diagonal residual
couplings, while the two traces eliminate the final diagonal entries. -/
theorem fiveDim_jointExtremalEigenbasis_zeroProducts
    (A B : Matrix (Fin 5) (Fin 5) ℂ)
    (hAstar : ∀ i j, A i j = star (A j i))
    (hBstar : ∀ i j, B i j = star (B j i))
    (hA0 : ∀ i, A i 0 = if i = 0 then 1 else 0)
    (hA1 : ∀ i, A i 1 = if i = 1 then -1 else 0)
    (hA2 : ∀ i, A i 2 = 0)
    (hA3 : ∀ i, A i 3 = 0)
    (hB0 : ∀ i, B i 0 = 0)
    (hB1 : ∀ i, B i 1 = 0)
    (hB2 : ∀ i, B i 2 = if i = 2 then 1 else 0)
    (hB3 : ∀ i, B i 3 = if i = 3 then -1 else 0)
    (htraceA : A.trace = 0)
    (htraceB : B.trace = 0) :
    A * B = 0 ∧ B * A = 0 := by
  have ha44 : A 4 4 = 0 := by
    have h := htraceA
    change (∑ i : Fin 5, A i i) = 0 at h
    rw [Fin.sum_univ_five] at h
    simpa [hA0, hA1, hA2, hA3] using h
  have hb44 : B 4 4 = 0 := by
    have h := htraceB
    change (∑ i : Fin 5, B i i) = 0 at h
    rw [Fin.sum_univ_five] at h
    simpa [hB0, hB1, hB2, hB3] using h
  have ha04 : A 0 4 = 0 := by rw [hAstar 0 4]; simp [hA0 4]
  have ha14 : A 1 4 = 0 := by rw [hAstar 1 4]; simp [hA1 4]
  have ha24 : A 2 4 = 0 := by rw [hAstar 2 4]; simp [hA2 4]
  have ha34 : A 3 4 = 0 := by rw [hAstar 3 4]; simp [hA3 4]
  have hb04 : B 0 4 = 0 := by rw [hBstar 0 4]; simp [hB0 4]
  have hb14 : B 1 4 = 0 := by rw [hBstar 1 4]; simp [hB1 4]
  have hb24 : B 2 4 = 0 := by rw [hBstar 2 4]; simp [hB2 4]
  have hb34 : B 3 4 = 0 := by rw [hBstar 3 4]; simp [hB3 4]
  have hAdiag : A = Matrix.diagonal fiveDimAWeight := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fiveDimAWeight, hA0, hA1, hA2, hA3,
        ha04, ha14, ha24, ha34, ha44]
  have hBdiag : B = Matrix.diagonal fiveDimBWeight := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [fiveDimBWeight, hB0, hB1, hB2, hB3,
        hb04, hb14, hb24, hb34, hb44]
  have hAB : ∀ i : Fin 5, fiveDimAWeight i * fiveDimBWeight i = 0 := by
    intro i
    fin_cases i <;> norm_num [fiveDimAWeight, fiveDimBWeight]
  have hBA : ∀ i : Fin 5, fiveDimBWeight i * fiveDimAWeight i = 0 := by
    intro i
    fin_cases i <;> norm_num [fiveDimAWeight, fiveDimBWeight]
  rw [hAdiag, hBdiag]
  constructor
  · rw [Matrix.diagonal_mul_diagonal]
    simp [hAB]
  · rw [Matrix.diagonal_mul_diagonal]
    simp [hBA]

end Neoplatonic.LTR
