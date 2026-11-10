import Neoplatonic.LTR.FiveFibreAtomicUnitary
import Neoplatonic.LTR.FiveFibreUnitaryTransport
import Mathlib.Tactic

/-!
# LTR-MAN-51: simultaneous unitary diagonalization of atomic truth projections

For a faithful resolution of identity by four mutually orthogonal
Hermitian idempotent matrices in dimension five, MAN-48/49 produces
an orthonormal basis subordinate to their ranges. MAN-50 packages
that basis into a unitary matrix whose columns are common eigenvectors.

The matrix identity P_v U = U diag(1_{label = v}) gives the exact
simultaneous unitary conjugacy for every atomic projector.
-/

namespace Neoplatonic.LTR

open scoped Matrix

private abbrev FiveMat := Matrix (Fin 5) (Fin 5) ℂ

/-- The diagonal characteristic function of atom v in the
faithful simultaneous-eigenbasis labeling. -/
noncomputable def FiveFibreAtomicResolution.atomicIndicator
    (P : FiveFibreAtomicResolution) (v : Fin 4) (j : Fin 5) : ℂ :=
  if v = P.atomicBasisLabel j then 1 else 0

/-- Each atomic projector intertwines the common eigenbasis
unitary with the corresponding diagonal truth indicator. -/
theorem FiveFibreAtomicResolution.atomicProjection_mul_unitary
    (P : FiveFibreAtomicResolution) (v : Fin 4) :
    P.proj v * (P.atomicBasisUnitary : FiveMat) =
      (P.atomicBasisUnitary : FiveMat) *
        Matrix.diagonal (P.atomicIndicator v) := by
  ext i j
  have hcol :
      (P.proj v * (P.atomicBasisUnitary : FiveMat)) *ᵥ Pi.single j 1 =
        ((P.atomicBasisUnitary : FiveMat) *
          Matrix.diagonal (P.atomicIndicator v)) *ᵥ Pi.single j 1 := by
    have hs :
        Pi.single j (P.atomicIndicator v j * (1 : ℂ)) =
          P.atomicIndicator v j • Pi.single j (1 : ℂ) := by
      simpa only [smul_eq_mul] using
        (Pi.single_smul' j (P.atomicIndicator v j) (1 : ℂ))
    simp only [← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single]
    rw [P.atomicBasisUnitary_mulVec, hs,
      Matrix.mulVec_smul, P.atomicBasisUnitary_mulVec]
    simpa only [atomicIndicator] using P.atomicBasis_mulVec_eigen v j
  have hi := congrArg (fun x : Fin 5 → ℂ => x i) hcol
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using hi

/-- Each of the four original atomic projectors is exactly the
unitary conjugate of its labelled diagonal truth indicator. -/
theorem FiveFibreAtomicResolution.atomicProjection_eq_unitaryConj
    (P : FiveFibreAtomicResolution) (v : Fin 4) :
    P.proj v =
      (fiveFibre_unitaryAut P.atomicBasisUnitary)
        (Matrix.diagonal (P.atomicIndicator v)) := by
  let U := P.atomicBasisUnitary
  have hmul := P.atomicProjection_mul_unitary v
  change P.proj v * (U : FiveMat) =
    (U : FiveMat) * Matrix.diagonal (P.atomicIndicator v) at hmul
  calc
    P.proj v = P.proj v * ((U : FiveMat) * star (U : FiveMat)) := by
      have hu : (U : FiveMat) * star (U : FiveMat) = 1 := by
        simpa only [Unitary.coe_star] using (Unitary.coe_mul_star_self U)
      rw [hu, mul_one]
    _ = (P.proj v * (U : FiveMat)) * star (U : FiveMat) := by
      rw [mul_assoc]
    _ = ((U : FiveMat) * Matrix.diagonal (P.atomicIndicator v)) *
          star (U : FiveMat) := by rw [hmul]
    _ = (fiveFibre_unitaryAut P.atomicBasisUnitary)
          (Matrix.diagonal (P.atomicIndicator v)) := by
      dsimp [U, fiveFibre_unitaryAut]

/-- In the recovered orthonormal coordinate chart, each original
atomic projection is precisely its diagonal indicator matrix. -/
theorem FiveFibreAtomicResolution.atomicProjection_diagonalized
    (P : FiveFibreAtomicResolution) (v : Fin 4) :
    (fiveFibre_unitaryAut P.atomicBasisUnitary).symm (P.proj v) =
      Matrix.diagonal (P.atomicIndicator v) := by
  rw [P.atomicProjection_eq_unitaryConj v]
  simp

end Neoplatonic.LTR
