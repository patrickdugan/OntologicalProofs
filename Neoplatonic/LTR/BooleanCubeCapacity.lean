import Neoplatonic.LTR.BooleanCubeGlobal
import Mathlib.Data.Fin.Tuple.Basic

/-!
# LTR-MAN-09C: exact hypercube edge and coordinate counts

A Boolean m-cube has 2^m vertices. Each undirected edge is indexed
uniquely by one coordinate and an assignment whose bit is zero there.

Fixing one bit leaves m-1 independent bits. Hence for m=n+1 there
are exactly (n+1)*2^n edges, and a 2-coordinate Dirac block per edge
has exactly (n+1)*2^(n+1) scalar Hilbert coordinates.

The m=0 cube has one vertex and no edges; this degenerate case is
handled explicitly.
-/

namespace Neoplatonic.LTR

/-- Free the remaining n bits after fixing one of the n+1
coordinates to false. -/
noncomputable def booleanCubeFixedFalseEquiv (n : ℕ)
    (i : Fin (n + 1)) :
    {u : BooleanCubeVertex (n + 1) // u i = false} ≃
      (Fin n → Bool) where
  toFun u := i.removeNth u.1
  invFun rest := ⟨i.insertNth false rest, by simp⟩
  left_inv u := by
    apply Subtype.ext
    change i.insertNth false (i.removeNth u.1) = u.1
    simpa only [← u.property] using
      (Fin.insertNth_self_removeNth i u.1)
  right_inv rest := by simp

/-- Exactly 2^n Boolean words have any specified (n+1)-st
coordinate fixed to false. -/
theorem booleanCubeFixedFalse_card (n : ℕ) (i : Fin (n + 1)) :
    Fintype.card
      {u : BooleanCubeVertex (n + 1) // u i = false} = 2 ^ n := by
  classical
  calc
    Fintype.card {u : BooleanCubeVertex (n + 1) // u i = false} =
        Fintype.card (Fin n → Bool) :=
      Fintype.card_congr (booleanCubeFixedFalseEquiv n i)
    _ = 2 ^ n := by simp [Fintype.card_fun]

/-- Unique unoriented edges: an (n+1)-cube has
(n+1)*2^n edge blocks. -/
theorem booleanCubeEdge_card_succ (n : ℕ) :
    Fintype.card (BooleanCubeEdge (n + 1)) =
      (n + 1) * 2 ^ n := by
  classical
  calc
    Fintype.card (BooleanCubeEdge (n + 1)) =
        ∑ i : Fin (n + 1),
          Fintype.card
            {u : BooleanCubeVertex (n + 1) // u i = false} := by
              simp [BooleanCubeEdge, Fintype.card_sigma]
    _ = ∑ _ : Fin (n + 1), 2 ^ n := by
      apply Finset.sum_congr rfl
      intro i _
      exact booleanCubeFixedFalse_card n i
    _ = (n + 1) * 2 ^ n := by simp

/-- The zero-dimensional cube has no edge blocks. -/
theorem booleanCubeEdge_card_zero :
    Fintype.card (BooleanCubeEdge 0) = 0 := by
  simp [BooleanCubeEdge]

/-- Each edge has two scalar Hilbert coordinates. The count is
m*2^m for m=n+1, as in the mathematical construction. -/
theorem booleanCubeHilbert_coordinate_card_succ (n : ℕ) :
    Fintype.card (BooleanCubeEdge (n + 1) × Fin 2) =
      (n + 1) * 2 ^ (n + 1) := by
  classical
  rw [Fintype.card_prod, booleanCubeEdge_card_succ]
  simp [pow_succ]
  ring

/-- The absolute coordinate count is zero for the 0-cube's
edge-based Dirac Hilbert realization. -/
theorem booleanCubeHilbert_coordinate_card_zero :
    Fintype.card (BooleanCubeEdge 0 × Fin 2) = 0 := by
  simp [booleanCubeEdge_card_zero]

end Neoplatonic.LTR
