import Neoplatonic.LTR.BooleanCubeUnitPairs

/-!
# LTR-MAN-09F: exact Hamming metric from a finite Dirac commutator

For each Boolean hypercube dimension m, the finite edge Hilbert sum
has D = sum of unit-coupled two-point Dirac blocks and π(f) the
endpoint-diagonal representation.

The upper Connes-distance estimate comes from Hamming geodesics.
For the lower estimate take the complex-valued distance-to-y observable,
f_y(x) = hammingDist x y, whose gradient along each edge is at most one.
It attains the full Hamming distance from x to y.

The result is stated as an exact universal upper bound with an
attaining witness, which is equivalent to the usual dual supremum
formulation of Connes' distance in this finite setting.

All the operators live on the genuine finite-edge complex Hilbert sum,
rather than only on a numerical graph-seminorm surrogate.
-/

namespace Neoplatonic.LTR

/-- Distance-to-y, complexified, is an actual finite-cube observable. -/
def booleanCubeDistanceObservable {m : ℕ}
    (y : BooleanCubeVertex m) :
    BooleanCubeVertex m → ℂ :=
  fun x => (hammingDist x y : ℂ)

/-- Unit edges change the distance-to-y function by at most one. -/
theorem booleanCubeDistanceObservable_unit_edge {m : ℕ}
    (y : BooleanCubeVertex m) (e : BooleanCubeEdge m) :
    ‖booleanCubeDistanceObservable y (booleanCubeEdgeUpper e) -
      booleanCubeDistanceObservable y (booleanCubeEdgeLower e)‖ ≤ 1 := by
  let lo := booleanCubeEdgeLower e
  let up := booleanCubeEdgeUpper e
  have hed : hammingDist lo up = 1 :=
    booleanCubeEdge_hamming_one e
  have hrev : hammingDist up lo = 1 := by
    rw [hammingDist_comm]
    exact hed
  have hUp : (hammingDist up y : ℝ) ≤
      1 + (hammingDist lo y : ℝ) := by
    have h := hammingDist_triangle up lo y
    rw [hrev] at h
    exact_mod_cast h
  have hLo : (hammingDist lo y : ℝ) ≤
      1 + (hammingDist up y : ℝ) := by
    have h := hammingDist_triangle lo up y
    rw [hed] at h
    exact_mod_cast h
  have habs : |(hammingDist up y : ℝ) -
      (hammingDist lo y : ℝ)| ≤ 1 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  change ‖((hammingDist up y : ℝ) : ℂ) -
    ((hammingDist lo y : ℝ) : ℂ)‖ ≤ 1
  simpa only [← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using habs

/-- The actual finite Hilbert Dirac commutator norm of every
distance-to-y witness is at most one. -/
theorem booleanCubeDistanceObservable_commutator_le_one {m : ℕ}
    (y : BooleanCubeVertex m) :
    ‖booleanCubeCommutator (booleanCubeDistanceObservable y)‖ ≤ 1 := by
  apply (booleanCubeCommutator_norm_one_iff_edges _).mpr
  intro e
  exact booleanCubeDistanceObservable_unit_edge y e

/-- The distance witness attains the full Hamming distance. -/
theorem booleanCubeDistanceObservable_attains {m : ℕ}
    (x y : BooleanCubeVertex m) :
    ‖booleanCubeDistanceObservable y x -
      booleanCubeDistanceObservable y y‖ =
      (hammingDist x y : ℝ) := by
  simp [booleanCubeDistanceObservable, hammingDist_self]

/-- Exact finite-Hilbert Connes distance, certified as an upper
bound for all unit-commutator observables together with an attaining
observable at every pair of vertices. -/
theorem booleanCubeConnesDistance_operator_witness
    (m : ℕ) (x y : BooleanCubeVertex m) :
    (∀ f : BooleanCubeVertex m → ℂ,
      ‖booleanCubeCommutator f‖ ≤ 1 →
        ‖f x - f y‖ ≤ (hammingDist x y : ℝ)) ∧
    ∃ f : BooleanCubeVertex m → ℂ,
      ‖booleanCubeCommutator f‖ ≤ 1 ∧
      ‖f x - f y‖ = (hammingDist x y : ℝ) := by
  constructor
  · intro f hf
    exact booleanCubeCommutator_hamming_upper f hf x y
  · exact ⟨booleanCubeDistanceObservable y,
      booleanCubeDistanceObservable_commutator_le_one y,
      booleanCubeDistanceObservable_attains x y⟩

end Neoplatonic.LTR
