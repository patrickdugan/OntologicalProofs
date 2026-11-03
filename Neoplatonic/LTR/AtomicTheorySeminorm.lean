import Neoplatonic.LTR.AtomicSeminorm

/-!
# The exact logical spectral grade on genuine first-order completions

The kth nullary sentence has an idempotent continuous truth projection
in the algebra of real-valued functions on the actual first-order
completion space. Under the checked Cantor homeomorphism, its
Lipschitz seminorm is exactly 2^k with the dyadic first-disagreement
metric. One pair of actual complete theories attains the bound.

This establishes exact spectral *metric* filtration of the marked
first-order predicates. Its interpretation as a Dirac commutator seminorm
uses the analytic realization L_D=Lip from FILTERED_SPECTRAL.md, which
is a written operator-domain proof rather than a Lean theorem.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language

/-- A coordinate projection on the actual first-order complete-type space
equals the corresponding real bit observable after decoding. -/
theorem nullary_atomic_projection_eq_bitObservable
    (n : ℕ) (p : Nullary.T.CompleteType Empty) :
    logicalProjection (T := Nullary.T) (Nullary.liftedAtom n) p =
      bitObservable n (Nullary.decode p) := by
  classical
  by_cases hp : Nullary.liftedAtom n ∈ p
  · have hb : Nullary.decode p n = true := by
      simp [Nullary.decode, hp]
    rw [logicalProjection_apply_mem (T := Nullary.T)
      (Nullary.liftedAtom n) p hp]
    simp [bitObservable, hb]
  · have hb : Nullary.decode p n = false := by
      simp [Nullary.decode, hp]
    rw [logicalProjection_apply_not_mem (T := Nullary.T)
      (Nullary.liftedAtom n) p hp]
    simp [bitObservable, hb]

/-- The nth actual first-order sentence projector obeys the sharp
2^n Lipschitz bound, in the metric induced by the truth-value marking. -/
theorem nullary_atomic_projection_lipschitz
    (n : ℕ) (p q : Nullary.T.CompleteType Empty) :
    |logicalProjection (T := Nullary.T) (Nullary.liftedAtom n) p -
      logicalProjection (T := Nullary.T) (Nullary.liftedAtom n) q| ≤
      (2 : ℝ)^n * markedDistance Nullary.decode p q := by
  simpa only [nullary_atomic_projection_eq_bitObservable] using
    bitObservable_lipschitz_upper n (Nullary.decode p) (Nullary.decode q)

/-- A concrete pair of complete first-order theories achieves the
2^n logical metric expansion for the nth predicate. -/
theorem nullary_atomic_projection_lipschitz_sharp (n : ℕ) :
    let p := Nullary.encode (fun _ => false)
    let q := Nullary.encode (singleTrueBit n)
    |logicalProjection (T := Nullary.T) (Nullary.liftedAtom n) p -
      logicalProjection (T := Nullary.T) (Nullary.liftedAtom n) q| =
      (2 : ℝ)^n * markedDistance Nullary.decode p q := by
  dsimp
  rw [nullary_atomic_projection_eq_bitObservable,
    nullary_atomic_projection_eq_bitObservable]
  simp only [Nullary.decode_encode]
  exact bitObservable_lipschitz_sharp n

end Neoplatonic.LTR
