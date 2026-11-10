import Neoplatonic.LTR.FiveFibrePermutationNorm
import Neoplatonic.LTR.FiveFibreTruthTranslations
import Mathlib.Tactic

/-!
# LTR-MAN-42: coordinate-permutation invariance of the labelled Connes metric

A diagonal faithful representation of the four-atom truth algebra
on five complex Hilbert coordinates is determined by a truth-label
function label : Fin 5 → Fin 4. Its represented observable is the
diagonal matrix with entry f(label i) at basis coordinate i.

Define the Connes dual pseudometric for arbitrary labels as an
extended-real supremum over four-truth-value observables constrained
by the genuine continuous Hilbert-space Dirac commutator norm.
By MAN-41, simultaneous permutation of the five Hilbert basis
coordinates preserves that norm. The same four-truth-value functions
therefore satisfy exactly the same unit-ball condition, and the
supremum is invariant for every pair of truth atoms.

The canonical chart's equivalence with the previous five-coordinate
dual-distance definition and Boolean truth-label translations are
the next integration steps.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

/-- Dirac commutator of a four-atom truth observable represented
diagonally through an arbitrary five-coordinate label function. -/
noncomputable def fiveFibreLabelledDiracComm
    (label : Fin 5 → Fin 4)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Fin 4 → ℂ) :
    EuclideanSpace ℂ (Fin 5) →L[ℂ] EuclideanSpace ℂ (Fin 5) :=
  fiveFibreSquareDiracComm D (fun i => f (label i))

/-- Labelled truth observables whose actual represented
commutator has continuous Hilbert operator norm at most one. -/
def fiveFibreLabelledAdmissible
    (label : Fin 5 → Fin 4)
    (D : Matrix (Fin 5) (Fin 5) ℂ) : Type :=
  { f : Fin 4 → ℂ // ‖fiveFibreLabelledDiracComm label D f‖ ≤ 1 }

/-- Genuine Connes dual distance on the four-atom truth algebra in
the labelled diagonal representation. Infinite distances are allowed. -/
noncomputable def fiveFibreLabelledConnesDistance
    (label : Fin 5 → Fin 4)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (u v : Fin 4) : ℝ≥0∞ :=
  ⨆ f : fiveFibreLabelledAdmissible label D,
    (‖f.val u - f.val v‖₊ : ℝ≥0∞)

/-- When Hilbert basis indices are simultaneously permuted in the
Dirac matrix and truth labeling, every four-atom observable keeps
the exact same represented commutator norm. -/
theorem fiveFibreLabelledDiracComm_reindex_norm
    (e : Fin 5 ≃ Fin 5)
    (label : Fin 5 → Fin 4)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Fin 4 → ℂ) :
    ‖fiveFibreLabelledDiracComm
      (fun i => label (e.symm i)) (Matrix.reindex e e D) f‖ =
      ‖fiveFibreLabelledDiracComm label D f‖ := by
  unfold fiveFibreLabelledDiracComm fiveFibreSquareDiracComm
  exact fiveFibre_reindex_commutator_norm e D
    (fun i => f (label i))

/-- Every pairwise Connes dual distance is invariant under an
arbitrary permutation of the five Hilbert coordinates, including
the cases where the doubled atomic truth fibre lies at different
basis positions. -/
theorem fiveFibreLabelledConnesDistance_reindex
    (e : Fin 5 ≃ Fin 5)
    (label : Fin 5 → Fin 4)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (u v : Fin 4) :
    fiveFibreLabelledConnesDistance
      (fun i => label (e.symm i)) (Matrix.reindex e e D) u v =
    fiveFibreLabelledConnesDistance label D u v := by
  unfold fiveFibreLabelledConnesDistance
  apply le_antisymm
  · apply iSup_le
    intro f
    have hnorm := fiveFibreLabelledDiracComm_reindex_norm e label D f.val
    have hunit :
        ‖fiveFibreLabelledDiracComm label D f.val‖ ≤ 1 := by
      have h := f.property
      rw [hnorm] at h
      exact h
    let g : fiveFibreLabelledAdmissible label D := ⟨f.val, hunit⟩
    exact le_iSup
      (fun h : fiveFibreLabelledAdmissible label D =>
        (‖h.val u - h.val v‖₊ : ℝ≥0∞)) g
  · apply iSup_le
    intro f
    have hnorm := fiveFibreLabelledDiracComm_reindex_norm e label D f.val
    have hunit :
        ‖fiveFibreLabelledDiracComm
          (fun i => label (e.symm i)) (Matrix.reindex e e D) f.val‖ ≤ 1 := by
      have h := f.property
      rwa [hnorm]
    let g : fiveFibreLabelledAdmissible
        (fun i => label (e.symm i)) (Matrix.reindex e e D) :=
      ⟨f.val, hunit⟩
    exact le_iSup
      (fun h : fiveFibreLabelledAdmissible
        (fun i => label (e.symm i)) (Matrix.reindex e e D) =>
        (‖h.val u - h.val v‖₊ : ℝ≥0∞)) g

end Neoplatonic.LTR
