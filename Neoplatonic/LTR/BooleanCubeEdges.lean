import Neoplatonic.LTR.ManifestationOptimalRange
import Neoplatonic.LTR.ComplexValuedDiracCommutatorBlock
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.Card

/-!
# LTR-MAN-09: concrete hypercube edge Dirac blocks

Truth assignments to m independent propositions form the Boolean
hypercube V_m = Fin m -> Bool. An undirected hypercube edge is indexed
once, by a coordinate i and an assignment u having u_i = false.
The opposite endpoint is obtained by setting that bit to true.

Each edge carries the existing genuine complex 2x2 Euclidean Hilbert
Dirac block D_e = [[0,1],[1,0]] and diagonal observable
pi_e(f) = diag(f(u),f(v)).

The actual operator commutator has norm equal to the complex difference
across that edge. This supplies the building block for an exact
Hamming-metric spectral triple.

The full Hilbert space, graph metric proof, and dimension count are
formalized in subsequent modules.
-/

namespace Neoplatonic.LTR

/-- Vertices are complete truth assignments on m named propositions. -/
abbrev BooleanCubeVertex (m : ℕ) := Fin m → Bool

/-- Each undirected edge occurs once: its lower endpoint has bit i=false. -/
abbrev BooleanCubeEdge (m : ℕ) :=
  Σ i : Fin m, {u : BooleanCubeVertex m // u i = false}

/-- The zero-bit endpoint of a hypercube edge. -/
def booleanCubeEdgeLower {m : ℕ}
    (e : BooleanCubeEdge m) : BooleanCubeVertex m := e.2.1

/-- The endpoint obtained by setting the distinguished bit to true. -/
def booleanCubeEdgeUpper {m : ℕ}
    (e : BooleanCubeEdge m) : BooleanCubeVertex m :=
  Function.update e.2.1 e.1 true

/-- The two endpoints differ at the designated coordinate. -/
theorem booleanCubeEdge_endpoint_bit {m : ℕ}
    (e : BooleanCubeEdge m) :
    booleanCubeEdgeLower e e.1 = false ∧
      booleanCubeEdgeUpper e e.1 = true := by
  constructor
  · exact e.2.property
  · simp [booleanCubeEdgeUpper]

/-- The two endpoints agree at all other coordinates. -/
theorem booleanCubeEdge_agree_other {m : ℕ}
    (e : BooleanCubeEdge m) (j : Fin m) (h : j ≠ e.1) :
    booleanCubeEdgeLower e j = booleanCubeEdgeUpper e j := by
  simp [booleanCubeEdgeLower, booleanCubeEdgeUpper, h]

/-- Each designated pair is a genuine edge of Hamming length one. -/
theorem booleanCubeEdge_hamming_one {m : ℕ}
    (e : BooleanCubeEdge m) :
    hammingDist (booleanCubeEdgeLower e)
      (booleanCubeEdgeUpper e) = 1 := by
  classical
  have hfilter :
      (Finset.univ.filter
        (fun j : Fin m => booleanCubeEdgeLower e j ≠
          booleanCubeEdgeUpper e j)) = {e.1} := by
    ext j
    by_cases hj : j = e.1
    · subst j
      simp [booleanCubeEdge_endpoint_bit e]
    · simp [hj, booleanCubeEdge_agree_other e j hj]
  simpa [hammingDist, hfilter]

/-- The existing mass-zero, unit-coupling Dirac operator on one
actual two-dimensional complex Euclidean Hilbert block. -/
noncomputable def booleanCubeLocalDirac :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  complexEuclideanDiracBlock 0 1

/-- The scalar truth observable on the two endpoints of a cube edge. -/
noncomputable def booleanCubeLocalObservable {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) (e : BooleanCubeEdge m) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  complexValuedObservableBlock
    (f (booleanCubeEdgeLower e)) (f (booleanCubeEdgeUpper e))

/-- The actual complex-linear commutator on one edge. -/
noncomputable def booleanCubeLocalCommutator {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) (e : BooleanCubeEdge m) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  booleanCubeLocalDirac.comp (booleanCubeLocalObservable f e) -
    (booleanCubeLocalObservable f e).comp booleanCubeLocalDirac

/-- The exact local Dirac commutator norm is the edge gradient.
The original complex 2x2 block calculation is reused unchanged. -/
theorem booleanCubeLocalCommutator_norm {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) (e : BooleanCubeEdge m) :
    ‖booleanCubeLocalCommutator f e‖ =
      ‖f (booleanCubeEdgeUpper e) - f (booleanCubeEdgeLower e)‖ := by
  simpa [booleanCubeLocalCommutator,
    booleanCubeLocalDirac, booleanCubeLocalObservable] using
    (complexDirac_complexObservableBlock_commutator_norm
      0 1 (f (booleanCubeEdgeLower e)) (f (booleanCubeEdgeUpper e)))

/-- The local norm detects the same edge gradient in either orientation. -/
theorem booleanCubeLocalCommutator_norm_reverse {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) (e : BooleanCubeEdge m) :
    ‖booleanCubeLocalCommutator f e‖ =
      ‖f (booleanCubeEdgeLower e) - f (booleanCubeEdgeUpper e)‖ := by
  rw [booleanCubeLocalCommutator_norm, norm_sub_rev]

end Neoplatonic.LTR
