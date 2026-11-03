import Neoplatonic.LTR.InfiniteFiniteRank

/-!
# Compact squared resolvent on an actual infinite Hilbert space

The square of the block Dirac operator is scalar on its j-th
two-dimensional block, with eigenvalue 4^j + s_j^2. Hence
the bounded squared resolvent R=(I+D²)^(-1) acts by scalar weights
w_j=(1+4^j+s_j²)^(-1) on H = ℓ²(ℕ, ℝ²).

This module links the genuine bounded Hilbert operator to the
already verified compact finite-block maps. Their difference is the
exact infinite tail, with norm ≤ (1+4^N)^(-1). By norm closure of
compact operators, R itself is compact.

This theorem proves compactness of the *squared-resolvent candidate*.
Identifying it as the resolvent of a closed densely defined
self-adjoint unbounded operator D requires the maximal-domain theory.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- A rank-two block is supported on exactly its chosen coordinate. -/
theorem singleSquaredResolventBlock_apply
    (scale : ℕ → ℝ) (j : ℕ)
    (ψ : DiracBlockHilbert) (k : ℕ) :
    singleSquaredResolventBlock scale j ψ k =
      Pi.single j (chosenSquaredResolventWeight scale j • ψ j) k := by
  change (lp.single 2 j
    (scalarBlockCLM (chosenSquaredResolventWeight scale j) (ψ j))) k = _
  simp [lp.single_apply, scalarBlockCLM]

/-- The sum of the first N rank-two blocks is precisely their
piecewise-supported scalar diagonal action. -/
theorem finiteSquaredResolvent_apply
    (scale : ℕ → ℝ) (N : ℕ)
    (ψ : DiracBlockHilbert) (j : ℕ) :
    finiteSquaredResolvent scale N ψ j =
      if j < N then chosenSquaredResolventWeight scale j • ψ j else 0 := by
  change (∑ k ∈ Finset.range N, singleSquaredResolventBlock scale k ψ) j = _
  simp only [lp.coeFn_sum, Finset.sum_apply,
    singleSquaredResolventBlock_apply, Finset.sum_pi_single,
    Finset.mem_range]
  rfl

/-- Compact rank-two truncations are exactly the full Hilbert
squared resolvent minus its exponentially small infinite tail. -/
theorem finiteSquaredResolvent_eq_cutoff
    (scale : ℕ → ℝ) (N : ℕ) :
    finiteSquaredResolvent scale N =
      chosenSquaredResolventCLM scale -
        chosenSquaredResolventTailCLM scale N := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  exact (finiteSquaredResolvent_apply scale N ψ j).trans
    (squaredResolventCutoff_apply scale N ψ j).symm

/-- Norm convergence of explicit compact finite-rank approximants
with an exponential, scale-independent rate. -/
theorem chosenSquaredResolvent_finite_norm_bound
    (scale : ℕ → ℝ) (N : ℕ) :
    ‖chosenSquaredResolventCLM scale - finiteSquaredResolvent scale N‖ ≤
      squaredResolventTail N := by
  rw [finiteSquaredResolvent_eq_cutoff]
  have h :
      chosenSquaredResolventCLM scale -
        (chosenSquaredResolventCLM scale -
          chosenSquaredResolventTailCLM scale N) =
        chosenSquaredResolventTailCLM scale N := by abel
  rw [h]
  exact chosenSquaredResolventTailCLM_norm_le scale N

/-- A genuine compact bounded operator on ℓ², obtained from the
squared resolvent coefficients of exponentially growing Dirac
blocks with arbitrary real off-diagonal couplings. -/
theorem chosenSquaredResolvent_compact
    (scale : ℕ → ℝ) :
    IsCompactOperator (chosenSquaredResolventCLM scale) := by
  exact compact_of_squaredResolvent_tail
    (chosenSquaredResolventCLM scale)
    (finiteSquaredResolvent scale)
    (finiteSquaredResolvent_compact scale)
    (chosenSquaredResolvent_finite_norm_bound scale)

end Neoplatonic.LTR
