import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Neoplatonic.LTR.InfiniteResolvent

/-!
# Block-diagonal bounded operators on an infinite real Hilbert sum

The infinite Dirac construction acts on the actual real Hilbert space
H = lp 2 of EuclideanSpace ℝ (Fin 2). Each square-resolvent block
is a scalar multiplier of the identity, and its coefficient is at
most one. Mathlib lp.mapCLM constructs the corresponding bounded
continuous linear operator with a uniform operator norm bound.

Finite-rank truncation and the actual operator tail estimate are
subsequent proof obligations.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Infinite real Hilbert direct sum of two-component blocks. -/
abbrev DiracBlockHilbert :=
  lp (fun _ : ℕ => EuclideanSpace ℝ (Fin 2)) 2

/-- Scalar action on a single finite-dimensional Euclidean block. -/
noncomputable def scalarBlockCLM (w : ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  w • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))

/-- Multiplication by a real scalar has operator norm at most its abs. -/
theorem scalarBlockCLM_norm_le (w : ℝ) :
    ‖scalarBlockCLM w‖ ≤ |w| := by
  have h := norm_smul_le w
    (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)))
  have hid : ‖ContinuousLinearMap.id ℝ
      (EuclideanSpace ℝ (Fin 2))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  calc
    ‖scalarBlockCLM w‖ ≤ ‖w‖ *
        ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))‖ := h
    _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hid (norm_nonneg w)
    _ = |w| := by simp [Real.norm_eq_abs]

/-- A bounded Hilbert direct-sum operator with scalar coefficients. -/
noncomputable def boundedBlockDiagonal
    (w : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hw : ∀ j, |w j| ≤ K) :
    DiracBlockHilbert →L[ℝ] DiracBlockHilbert :=
  lp.mapCLM 2 (fun j => scalarBlockCLM (w j)) hK
    (fun j => (scalarBlockCLM_norm_le (w j)).trans (hw j))

/-- Pointwise coefficient bounds give a uniform operator norm bound
on the full infinite Hilbert direct sum. -/
theorem boundedBlockDiagonal_norm_le
    (w : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hw : ∀ j, |w j| ≤ K) :
    ‖boundedBlockDiagonal w K hK hw‖ ≤ K := by
  exact lp.norm_mapCLM_le 2 (fun j => scalarBlockCLM (w j)) hK
    (fun j => (scalarBlockCLM_norm_le (w j)).trans (hw j))

end Neoplatonic.LTR
