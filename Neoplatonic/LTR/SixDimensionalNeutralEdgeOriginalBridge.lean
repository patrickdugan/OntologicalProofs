import Neoplatonic.LTR.SixDimensionalActualNeutralEdgeOrthogonality
import Mathlib.Tactic

/-!
# MAN-127: neutral edges of a Hermitian witness are original truth edges

The zero-product lemmas from MAN-125 refer to E(P,N,Y), built from
the corner-neutral compression Y=CWQ. MAN-121 refers to undirected
truth edges of W. This general 6x6 matrix lemma is the missing
algebraic equality between these two descriptions.

When P and N are orthogonal projections onto opposite and neutral
truth fibres, P C=P and Q N=N, the edge E(P,N,Y) coincides with
P W N + N W P for a Hermitian witness W.

The lemma is independent of saturated energies and multiplicity.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- An actual corner-to-neutral block agrees with the corresponding
original Dirac block whenever the two fibre projectors are contained
in their respective sectors. -/
theorem sixMatrix_cornerNeutralBlock_forward
    (P N C Q W : SixMat)
    (hPC : P * C = P)
    (hQN : Q * N = N) :
    P * (C * W * Q) * N = P * W * N := by
  calc
    P * (C * W * Q) * N = (P * C) * W * (Q * N) := by noncomm_ring
    _ = P * W * N := by rw [hPC, hQN]

/-- Taking the adjoint of the forward fibre equality produces
the reverse neutral-to-corner equality under Hermitianity. -/
theorem sixMatrix_neutralUndirectedEdge_eq_originalTruthEdge
    (P N C Q W : SixMat)
    (hP : P.IsHermitian) (hN : N.IsHermitian)
    (hW : W.IsHermitian)
    (hPC : P * C = P)
    (hQN : Q * N = N) :
    sixMatrix_neutralUndirectedEdge P N (C * W * Q) =
      P * W * N + N * W * P := by
  have hforward := sixMatrix_cornerNeutralBlock_forward
    P N C Q W hPC hQN
  have hreverse : N * (C * W * Q).conjTranspose * P =
      N * W * P := by
    have h := congrArg Matrix.conjTranspose hforward
    simpa only [Matrix.conjTranspose_mul, hP.eq, hN.eq, hW.eq, Matrix.mul_assoc] using h
  change P * (C * W * Q) * N +
      N * (C * W * Q).conjTranspose * P =
    P * W * N + N * W * P
  rw [hforward, hreverse]

end Neoplatonic.LTR
