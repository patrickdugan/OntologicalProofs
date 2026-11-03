import Neoplatonic.LTR.SpectralBridge
import Mathlib.Data.Finsupp.Defs

/-!
# The finitely supported core of the infinite Dirac operator

The infinite Dirac operator is a direct sum of real symmetric two-point
blocks with location-dependent masses and scales. This file defines its
actual algebraic action on finitely supported sequences of two-vectors,
proves finite support is preserved, and checks the exact block energy,
pairing symmetry, and a bilinear symmetry theorem on the finite core.

This core is a densely defined unbounded operator *after* embedding in
the Hilbert direct sum ℓ²(ℕ, ℝ²). Density, adjoint domains, compact
resolvent, and infinite commutator bounds are separate analytic steps.
No claim that formal core symmetry alone proves self-adjointness.
-/

namespace Neoplatonic.LTR

/-- The real two-point action underlying a mass-shifted Dirac block. -/
def realDiracPair (mass scale : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (mass * z.1 + scale * z.2, scale * z.1 - mass * z.2)

/-- Elementary real Euclidean pairing on two-component vectors. -/
def realPairing (z w : ℝ × ℝ) : ℝ := z.1 * w.1 + z.2 * w.2

theorem realDiracPair_zero (mass scale : ℝ) :
    realDiracPair mass scale (0 : ℝ × ℝ) = 0 := by
  ext <;> simp [realDiracPair]

theorem realDiracPair_add (mass scale : ℝ) (z w : ℝ × ℝ) :
    realDiracPair mass scale (z + w) =
      realDiracPair mass scale z + realDiracPair mass scale w := by
  apply Prod.ext <;> dsimp [realDiracPair] <;> ring

theorem realDiracPair_smul (mass scale r : ℝ) (z : ℝ × ℝ) :
    realDiracPair mass scale (r • z) =
      r • realDiracPair mass scale z := by
  apply Prod.ext <;> dsimp [realDiracPair] <;> ring

/-- A block action is symmetric with respect to the real pairing. -/
theorem realDiracPair_symmetric (mass scale : ℝ) (z w : ℝ × ℝ) :
    realPairing (realDiracPair mass scale z) w =
      realPairing z (realDiracPair mass scale w) := by
  dsimp [realPairing, realDiracPair]
  ring

/-- The core consists of finitely supported sequences of 2-vectors.
The coefficients may grow without bound with the index. -/
def coreDirac (mass scale : ℕ → ℝ)
    (z : ℕ →₀ (ℝ × ℝ)) : ℕ →₀ (ℝ × ℝ) :=
  Finsupp.onFinset z.support
    (fun j => realDiracPair (mass j) (scale j) (z j))
    (by
      intro j hj
      by_contra hnot
      have hz : z j = 0 := Finsupp.notMem_support_iff.mp hnot
      have hz' : realDiracPair (mass j) (scale j) (z j) = 0 := by
        rw [hz]
        exact realDiracPair_zero _ _
      exact hj hz')

@[simp]
theorem coreDirac_apply (mass scale : ℕ → ℝ)
    (z : ℕ →₀ (ℝ × ℝ)) (j : ℕ) :
    coreDirac mass scale z j =
      realDiracPair (mass j) (scale j) (z j) := rfl

/-- Even exponentially growing block masses preserve the finite-support core. -/
theorem coreDirac_support_subset (mass scale : ℕ → ℝ)
    (z : ℕ →₀ (ℝ × ℝ)) :
    (coreDirac mass scale z).support ⊆ z.support := by
  unfold coreDirac
  exact Finsupp.support_onFinset_subset

/-- The formal quadratic pairing on a finite union of supports. -/
def coreDiracForm (mass scale : ℕ → ℝ)
    (z w : ℕ →₀ (ℝ × ℝ)) : ℝ :=
  ∑ j ∈ z.support ∪ w.support,
    realPairing (realDiracPair (mass j) (scale j) (z j)) (w j)

/-- Infinite block-diagonal Dirac actions are symmetric on every
finitely supported vector pair, with exact finite sums. -/
theorem coreDiracForm_symmetric (mass scale : ℕ → ℝ)
    (z w : ℕ →₀ (ℝ × ℝ)) :
    coreDiracForm mass scale z w =
      coreDiracForm mass scale w z := by
  unfold coreDiracForm
  calc
    ∑ j ∈ z.support ∪ w.support,
        realPairing (realDiracPair (mass j) (scale j) (z j)) (w j) =
      ∑ j ∈ z.support ∪ w.support,
        realPairing (realDiracPair (mass j) (scale j) (w j)) (z j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact realDiracPair_symmetric (mass j) (scale j) (z j) (w j)
    _ = ∑ j ∈ w.support ∪ z.support,
        realPairing (realDiracPair (mass j) (scale j) (w j)) (z j) := by
          rw [Finset.union_comm]

/-- The block square is scalar, even with arbitrary growing coefficients. -/
theorem realDiracPair_square (mass scale : ℝ) (z : ℝ × ℝ) :
    realDiracPair mass scale (realDiracPair mass scale z) =
      (mass ^ 2 + scale ^ 2) • z := by
  apply Prod.ext <;> dsimp [realDiracPair] <;> ring

end Neoplatonic.LTR
