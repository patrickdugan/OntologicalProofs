import Mathlib
import Neoplatonic.LTR.UniqueGamesRecursive

/-!
# LTR-UG-01: translation games as gauge-invariant finite defects

A graph has edge translations in an arbitrary additive commutative group.
The observable is the edge defect `c - da`. Vertex gauge transformations
change both the connection and the labeling, preserving this defect exactly.
Finite edge sets turn defects into clopen Boolean satisfaction predicates.

This module establishes the algebraic bridge only. The operator norm,
curvature-decoding and UGC complexity corollaries are recorded separately.
-/

namespace Neoplatonic.LTR.UniqueGames

universe u v w
variable {V : Type u} {E : Type v} {K : Type w} [AddCommGroup K]

/-- Coboundary of a vertex labeling on an oriented edge. -/
def coboundary (source target : E → V) (a : V → K) (e : E) : K :=
  a (target e) - a (source e)

/-- A zero defect means that this edge is satisfied. -/
def defect (source target : E → V) (c : E → K) (a : V → K) (e : E) : K :=
  c e - coboundary source target a e

/-- Transform connection and labeling by the same vertex gauge. -/
theorem defect_gauge
    (source target : E → V) (c : E → K) (a p : V → K) (e : E) :
    defect source target
        (fun i => c i + coboundary source target p i)
        (fun x => a x + p x) e =
      defect source target c a e := by
  simp only [defect, coboundary]
  abel

theorem defect_zero_iff_satisfied
    (source target : E → V) (c : E → K) (a : V → K) (e : E) :
    defect source target c a e = 0 ↔
      a (target e) - a (source e) = c e := by
  simp [defect, coboundary, sub_eq_zero, eq_comm]

/-- The set of failed edge occurrences, counting parallel edges separately. -/
def badEdges [Fintype E] [DecidableEq K]
    (source target : E → V) (c : E → K) (a : V → K) : Finset E :=
  Finset.univ.filter (fun e => defect source target c a e ≠ 0)

theorem badEdges_gauge [Fintype E] [DecidableEq K]
    (source target : E → V) (c : E → K) (a p : V → K) :
    badEdges source target
        (fun i => c i + coboundary source target p i)
        (fun x => a x + p x) =
      badEdges source target c a := by
  ext e
  simp [badEdges, defect_gauge]

theorem badCount_gauge [Fintype E] [DecidableEq K]
    (source target : E → V) (c : E → K) (a p : V → K) :
    (badEdges source target
        (fun i => c i + coboundary source target p i)
        (fun x => a x + p x)).card =
      (badEdges source target c a).card := by
  rw [badEdges_gauge]

end Neoplatonic.LTR.UniqueGames
