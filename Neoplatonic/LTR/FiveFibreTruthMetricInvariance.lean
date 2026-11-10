import Neoplatonic.LTR.FiveFibreLabelledConnesDistance
import Mathlib.Tactic

/-!
# LTR-MAN-43: Connes dual distance is invariant under truth-algebra relabeling

A permutation of the four truth atoms acts on the represented algebra
by precomposition of the four complex truth values. If the atom labels
at each Hilbert coordinate are permuted at the same time, the set of
represented observables is unchanged.

Consequently the genuine Connes dual pseudometric is invariant,
with distances between two atoms transported to distances between
their images. This holds for every equivalence of Fin 4, and in
particular for the four Hamming-preserving Boolean-square translations
from MAN-40.

Together with MAN-42's Hilbert-coordinate permutation invariance,
this gives full metric covariance under both components of the
faithful diagonal chart reduction.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

/-- Relabeling all four truth atoms and their corresponding arguments
leaves the genuine Connes dual distance unchanged. -/
theorem fiveFibreLabelledConnesDistance_truthEquiv
    (τ : Fin 4 ≃ Fin 4)
    (label : Fin 5 → Fin 4)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (u v : Fin 4) :
    fiveFibreLabelledConnesDistance
      (fun i => τ (label i)) D (τ u) (τ v) =
    fiveFibreLabelledConnesDistance label D u v := by
  unfold fiveFibreLabelledConnesDistance
  apply le_antisymm
  · apply iSup_le
    intro f
    have hunit :
        ‖fiveFibreLabelledDiracComm label D
          (fun w => f.val (τ w))‖ ≤ 1 := by
      exact f.property
    let g : fiveFibreLabelledAdmissible label D :=
      ⟨fun w => f.val (τ w), hunit⟩
    exact le_iSup
      (fun h : fiveFibreLabelledAdmissible label D =>
        (‖h.val u - h.val v‖₊ : ℝ≥0∞)) g
  · apply iSup_le
    intro f
    have hunit :
        ‖fiveFibreLabelledDiracComm
          (fun i => τ (label i)) D
          (fun w => f.val (τ.symm w))‖ ≤ 1 := by
      change ‖fiveFibreSquareDiracComm D
        (fun i => f.val (τ.symm (τ (label i))))‖ ≤ 1
      simpa only [Equiv.symm_apply_apply] using f.property
    let g : fiveFibreLabelledAdmissible
        (fun i => τ (label i)) D :=
      ⟨fun w => f.val (τ.symm w), hunit⟩
    have h := le_iSup
      (fun h : fiveFibreLabelledAdmissible
        (fun i => τ (label i)) D =>
        (‖h.val (τ u) - h.val (τ v)‖₊ : ℝ≥0∞)) g
    simpa only [g, Equiv.symm_apply_apply] using h

/-- Boolean-square translations preserve the labelled Connes dual
pseudometric while simultaneously relabeling the four truth atoms. -/
theorem fiveFibreLabelledConnesDistance_squareTranslation
    (v : Fin 4)
    (label : Fin 5 → Fin 4)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (u w : Fin 4) :
    fiveFibreLabelledConnesDistance
      (fun i => twoBitSquareTranslation v (label i)) D
      (twoBitSquareTranslation v u)
      (twoBitSquareTranslation v w) =
    fiveFibreLabelledConnesDistance label D u w :=
  fiveFibreLabelledConnesDistance_truthEquiv
    (twoBitSquareTranslation v) label D u w

end Neoplatonic.LTR
