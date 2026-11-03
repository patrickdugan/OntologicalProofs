import Neoplatonic.LTR.NullaryTopology
import Neoplatonic.LTR.NullaryEndomorphisms

/-!
# Every syntactic halting-index map is topologically continuous

For any Boolean signal H, the corresponding accelerated stream map is
continuous in the product topology: its nth output coordinate reads
exactly one input coordinate. Under the proved Cantor homeomorphism
for the one-axiom first-order theory, this makes every syntactic
endomorphism continuous even though finite Lipschitz regularity is
undecidable.

The result separates ordinary topological continuity from the effective
question of a quantitative metric bound.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- Any coordinate-selector stream map is continuous. -/
theorem continuous_acceleratedStream (H : ℕ → Bool) :
    Continuous (acceleratedStream H) := by
  apply continuous_pi_iff.mpr
  intro n
  cases h : H n with
  | false =>
      simpa [acceleratedStream, h] using
        (continuous_apply n : Continuous (fun x : ℕ → Bool => x n))
  | true =>
      simpa [acceleratedStream, h] using
        (continuous_apply (2 * n) :
          Continuous (fun x : ℕ → Bool => x (2 * n)))

/-- The encoding is the continuous inverse of the completed-type
Cantor homeomorphism. -/
theorem continuous_encode : Continuous encode := by
  have heq : (encode : (ℕ → Bool) → T.CompleteType Empty) =
      cantorHomeomorph.symm := by
    funext b
    exact (cantorHomeomorph_symm_apply b).symm
  rw [heq]
  exact cantorHomeomorph.symm.continuous

/-- All halting-index syntactic endomorphisms of the complete-type
space are continuous, including ones with unbounded Lipschitz ratio. -/
theorem continuous_syntaxMap (e : Nat.Partrec.Code) :
    Continuous (syntaxMap e) := by
  exact continuous_encode.comp
    ((continuous_acceleratedStream (stagedHalting e)).comp continuous_decode)

end Neoplatonic.LTR.Nullary
