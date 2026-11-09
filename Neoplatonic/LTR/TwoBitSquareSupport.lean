import Neoplatonic.LTR.TwoDirectionTraceZero
import Mathlib.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# LTR-MAN-15B: exact four-cycle edge/branching obstruction

The support graph of the two-bit Boolean square has four possible
one-bit-flip edges:

  a = (00,01), b = (00,10), c = (01,11), d = (10,11).

At the four vertices, a branching event is exactly the presence of
both incident edges, respectively a∧b, a∧c, b∧d, c∧d.

Any square support with at least three edges must have at least
two distinct branching vertices. Equivalently, if at most one
vertex is allowed to support two incident couplings, the graph can
contain at most two edges and cannot connect all four truth profiles.

This is the finite combinatorial endpoint of the written 5D no-go.
The remaining analytic bridge is to derive the one-dimensional
fibre's degree-at-most-one restriction from AB = 0 and establish
AB = 0 using the extremal spectral space, rank and trace lemmas.
-/

namespace Neoplatonic.LTR

/-- Regard a Bool edge-presence flag as an integer 0 or 1. -/
def twoBitEdgeWeight (edge : Bool) : ℕ :=
  if edge then 1 else 0

/-- Number of present edges in a four-vertex Boolean square. -/
def twoBitSquareEdgeCount (a b c d : Bool) : ℕ :=
  twoBitEdgeWeight a + twoBitEdgeWeight b +
    twoBitEdgeWeight c + twoBitEdgeWeight d

/-- Number of vertices incident to BOTH of their square edges. -/
def twoBitSquareBranchCount (a b c d : Bool) : ℕ :=
  twoBitEdgeWeight (a && b) + twoBitEdgeWeight (a && c) +
    twoBitEdgeWeight (b && d) + twoBitEdgeWeight (c && d)

/-- A support with three or four square edges has at least two
degree-two vertices. This checks all sixteen exact Boolean patterns. -/
theorem twoBitSquare_threeEdges_force_twoBranches
    (a b c d : Bool)
    (h : 3 ≤ twoBitSquareEdgeCount a b c d) :
    2 ≤ twoBitSquareBranchCount a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [twoBitSquareEdgeCount,
      twoBitSquareBranchCount, twoBitEdgeWeight] at *

/-- If at most one vertex supports both directions, the square
support contains at most two edges, insufficient for connectivity. -/
theorem twoBitSquare_oneBranch_atMost_twoEdges
    (a b c d : Bool)
    (h : twoBitSquareBranchCount a b c d ≤ 1) :
    twoBitSquareEdgeCount a b c d ≤ 2 := by
  by_contra hbad
  have hthree : 3 ≤ twoBitSquareEdgeCount a b c d := by omega
  have htwo : 2 ≤ twoBitSquareBranchCount a b c d :=
    twoBitSquare_threeEdges_force_twoBranches a b c d hthree
  omega

end Neoplatonic.LTR
