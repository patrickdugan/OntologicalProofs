import Neoplatonic.LTR.SixDimensionalSignedOppositeGramCornerBridge
import Mathlib.Tactic

/-!
# LTR-MAN-107: the 3-unit triple-fibre separating probe

Consider a positive saturated opposite 00/11 Dirac witness and
a singleton 00 fibre. MAN-106 prepares the missing hypothesis:
the Dirac matrix has no 00-to-neutral (01/10) couplings.

The four-truth probe f=(0,3,3,2) differs from the signed Hamming
sum s=(0,1,1,2). On the existing Dirac coupling support,
the imaginary commutator of f is the signed diagonal conjugate
J W+ J where J=(1,-1,-1,1).

This module proves the exact finite truth table, the diagonal
sign involution, and its consequence for arbitrary six-dimensional
Dirac matrices with explicit vanishing 00-to-neutral entries.
All identities use the original labelled Hilbert coordinates.

The final Hamming contradiction requires the concrete MAN-106
support lemma and transport to the Dirac Lipschitz norm.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The proposed triple-corner separating observable with values
0,3,3,2 on truth atoms 00,01,10,11. -/
def squareTriple03Probe (u : Fin 4) : ℂ :=
  if u = 0 then 0 else if u = 3 then 2 else 3

/-- The diagonal sign change that flips the neutral truth fibres. -/
def squareTriple03Sign (u : Fin 4) : ℂ :=
  if u = 1 ∨ u = 2 then -1 else 1

/-- The only truth-atom pairs on which the separating probe
differs from diagonal sign conjugation of the Hamming sum. -/
def squareTriple03Bad (u v : Fin 4) : Prop :=
  (u = 0 ∧ (v = 1 ∨ v = 2)) ∨
    (v = 0 ∧ (u = 1 ∨ u = 2))

/-- The separating probe is exactly sign-conjugate to the
Hamming sum on all truth pairs except 00-to-neutral links. -/
theorem squareTriple03Probe_coefficient_of_notBad
    (u v : Fin 4)
    (hbad : ¬ squareTriple03Bad u v) :
    squareTriple03Probe v - squareTriple03Probe u =
      (squareTriple03Sign u * squareTriple03Sign v) *
        ((squareTruthBitP v + squareTruthBitQ v) -
          (squareTruthBitP u + squareTruthBitQ u)) := by
  fin_cases u <;> fin_cases v <;>
    simp_all [squareTriple03Bad, squareTriple03Probe,
      squareTriple03Sign, squareTruthBitP, squareTruthBitQ] <;> ring

/-- The sign is an exact involution on each truth atom. -/
theorem squareTriple03Sign_square_one (u : Fin 4) :
    squareTriple03Sign u * squareTriple03Sign u = 1 := by
  fin_cases u <;>
    norm_num [squareTriple03Sign]

/-- The actual six-dimensional signed diagonal basis operator. -/
def sixTriple03SignMatrix (label : Fin 6 → Fin 4) : SixMat :=
  Matrix.diagonal (fun i => squareTriple03Sign (label i))

/-- The diagonal sign matrix squares to the identity in any
labelled Hilbert chart, irrespective of fibre multiplicities. -/
theorem sixTriple03SignMatrix_involution
    (label : Fin 6 → Fin 4) :
    sixTriple03SignMatrix label *
      sixTriple03SignMatrix label = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [sixTriple03SignMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_apply, squareTriple03Sign_square_one,
      Matrix.one_apply]
  · simp [sixTriple03SignMatrix, Matrix.diagonal_mul,
      Matrix.diagonal_apply, Matrix.one_apply, hij]

/-- The imaginary commutator of the triple separating probe,
using the original Dirac matrix rather than a toy support graph. -/
def sixTriple03ProbeImagComm
    (label : Fin 6 → Fin 4) (D : SixMat) : SixMat :=
  fun i j => Complex.I *
    (squareTriple03Probe (label j) -
      squareTriple03Probe (label i)) * D i j

/-- If 00-to-neutral Dirac couplings vanish in both directions,
the probe commutator equals the diagonal sign conjugate of
the genuine positive saturated signed Hamming witness. -/
theorem sixTriple03Probe_signConjugate_plusWitness
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hzero : ∀ i j : Fin 6,
      squareTriple03Bad (label i) (label j) → D i j = 0) :
    sixTriple03ProbeImagComm label D =
      sixTriple03SignMatrix label *
        (labelledSquareA label D + labelledSquareB label D) *
          sixTriple03SignMatrix label := by
  ext i j
  simp only [sixTriple03ProbeImagComm, sixTriple03SignMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.add_apply, labelledSquareA, labelledSquareB]
  by_cases hbad : squareTriple03Bad (label i) (label j)
  · simp [hzero i j hbad]
  · have hc := squareTriple03Probe_coefficient_of_notBad
      (label i) (label j) hbad
    rw [hc]
    ring

/-- The separating probe has gap three between 00 and each
of the two neutral truth atoms. -/
theorem squareTriple03Probe_gap01 :
    squareTriple03Probe 1 - squareTriple03Probe 0 = (3 : ℂ) := by
  norm_num [squareTriple03Probe]

theorem squareTriple03Probe_gap02 :
    squareTriple03Probe 2 - squareTriple03Probe 0 = (3 : ℂ) := by
  norm_num [squareTriple03Probe]

end Neoplatonic.LTR
