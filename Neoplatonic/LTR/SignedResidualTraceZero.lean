import Neoplatonic.LTR.EigenquartetTrace
import Neoplatonic.LTR.TwoDirectionResidualCompression
import Mathlib.Tactic

/-!
# LTR-MAN-64: vanishing residual trace for genuine Hamming coordinate pairs

MAN-63 relates the trace of the residual compression to the ambient
operator trace and the eigenvalues on a constructed orthonormal quartet.
In the Hamming coordinate system the A eigenvalues are 1,-1,0,0
and the B eigenvalues are 0,0,1,-1. Both sums vanish.

The actual coordinate commutators are traceless. We derive trace zero
for both compressed operators in the invariant residual Hilbert
submodule. In complex dimension six, the residual has dimension two,
so MAN-61's traceless Hermitian Pauli form applies after choosing an
orthonormal basis of that residual submodule.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The eigenvalues of A on the quartet. -/
def twoDirectionAQuartetEigenvalues (i : Fin 4) : ℂ :=
  if i = 0 then 1 else if i = 1 then -1 else 0

/-- The eigenvalues of B on the quartet. -/
def twoDirectionBQuartetEigenvalues (i : Fin 4) : ℂ :=
  if i = 2 then 1 else if i = 3 then -1 else 0

@[simp] theorem twoDirectionAQuartetEigenvalues_sum :
    (∑ i : Fin 4, twoDirectionAQuartetEigenvalues i) = 0 := by
  simp [Fin.sum_univ_four, twoDirectionAQuartetEigenvalues]

@[simp] theorem twoDirectionBQuartetEigenvalues_sum :
    (∑ i : Fin 4, twoDirectionBQuartetEigenvalues i) = 0 := by
  simp [Fin.sum_univ_four, twoDirectionBQuartetEigenvalues]

/-- Signed extremal eigendirections of the real coordinate A,
including B's eigenvectors on which A vanishes. -/
theorem TwoDirectionExtremalSystem.eigenquartet_A
    (S : TwoDirectionExtremalSystem E) :
    ∀ i : Fin 4,
      S.A.toLinearMap
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus i) =
      twoDirectionAQuartetEigenvalues i •
        twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus i := by
  have hAvplus : S.A S.vplus = 0 :=
    twoDirection_unitEigenvector_annihilates_first
      S.A S.B S.plus_le S.minus_le 1 (by norm_num)
      S.vplus (by simpa using S.B_vplus)
  have hAvminus : S.A S.vminus = 0 :=
    twoDirection_unitEigenvector_annihilates_first
      S.A S.B S.plus_le S.minus_le (-1) (by norm_num)
      S.vminus (by simpa using S.B_vminus)
  intro i
  fin_cases i <;>
    simp [twoDirectionSignedQuartet, twoDirectionAQuartetEigenvalues,
      S.A_uplus, S.A_uminus, hAvplus, hAvminus]

/-- Signed extremal eigendirections of coordinate B. -/
theorem TwoDirectionExtremalSystem.eigenquartet_B
    (S : TwoDirectionExtremalSystem E) :
    ∀ i : Fin 4,
      S.B.toLinearMap
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus i) =
      twoDirectionBQuartetEigenvalues i •
        twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus i := by
  have hBuplus : S.B S.uplus = 0 :=
    twoDirection_unitEigenvector_annihilates_second
      S.A S.B S.plus_le S.minus_le 1 (by norm_num)
      S.uplus (by simpa using S.A_uplus)
  have hBuminus : S.B S.uminus = 0 :=
    twoDirection_unitEigenvector_annihilates_second
      S.A S.B S.plus_le S.minus_le (-1) (by norm_num)
      S.uminus (by simpa using S.A_uminus)
  intro i
  fin_cases i <;>
    simp [twoDirectionSignedQuartet, twoDirectionBQuartetEigenvalues,
      S.B_vplus, S.B_vminus, hBuplus, hBuminus]

/-- A traceless ambient coordinate A has a traceless residual
compression, on the actual invariant Hilbert subspace. -/
theorem TwoDirectionExtremalSystem.residualA_trace_zero
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (htr : LinearMap.trace ℂ E S.A.toLinearMap = 0) :
    LinearMap.trace ℂ S.residual S.residualA.toLinearMap = 0 := by
  let q := twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  have hR : ∀ x ∈ (Submodule.span ℂ (Set.range q))ᗮ,
      S.A.toLinearMap x ∈ (Submodule.span ℂ (Set.range q))ᗮ := by
    intro x hx
    exact (S.residual_invariant x
      (show x ∈ S.residual from hx)).1
  have hz := eigenquartet_residual_restrict_trace_zero
    q hq S.A.toLinearMap twoDirectionAQuartetEigenvalues
    S.eigenquartet_A htr twoDirectionAQuartetEigenvalues_sum hR
  change LinearMap.trace ℂ S.residual S.residualA.toLinearMap = 0 at hz
  exact hz

/-- A traceless ambient coordinate B likewise has a traceless
residual compression, with the same orthonormal quartet. -/
theorem TwoDirectionExtremalSystem.residualB_trace_zero
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (htr : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    LinearMap.trace ℂ S.residual S.residualB.toLinearMap = 0 := by
  let q := twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  have hR : ∀ x ∈ (Submodule.span ℂ (Set.range q))ᗮ,
      S.B.toLinearMap x ∈ (Submodule.span ℂ (Set.range q))ᗮ := by
    intro x hx
    exact (S.residual_invariant x
      (show x ∈ S.residual from hx)).2
  have hz := eigenquartet_residual_restrict_trace_zero
    q hq S.B.toLinearMap twoDirectionBQuartetEigenvalues
    S.eigenquartet_B htr twoDirectionBQuartetEigenvalues_sum hR
  change LinearMap.trace ℂ S.residual S.residualB.toLinearMap = 0 at hz
  exact hz

end Neoplatonic.LTR
