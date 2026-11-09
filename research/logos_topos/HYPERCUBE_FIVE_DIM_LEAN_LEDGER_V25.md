# LTR-MAN-25: five-dimensional Boolean-square obstruction, formalization ledger

**Date:** 2026-11-09  
**Scope:** two independent Boolean truth coordinates, four atomic truth sectors, finite faithful complex spectral geometry.

The written argument gives the proposed strict bound `r_geom(2) >= 6`. The
formal development now checks the zero-product spectral core and the
canonical five-dimensional doubled-fibre contradiction under explicit
hypotheses. A global universal lower-bound theorem is still pending.

## Kernel-verified chain

| Stage | PR | Verified mathematical statement |
|---|---|---|
| MAN-12 | [#37](https://github.com/patrickdugan/OntologicalProofs/pull/37) | `‖A+B‖, ‖A−B‖ ≤ 1` implies `‖Av‖²+‖Bv‖²≤‖v‖²` |
| MAN-13 | [#38](https://github.com/patrickdugan/OntologicalProofs/pull/38) | Unit-circle eigenspaces of each operator lie in the other's kernel and are orthogonal across the directions |
| MAN-14 | [#39](https://github.com/patrickdugan/OntologicalProofs/pull/39) | Idempotent-induced grading anticommutes with the commutator and pairs opposite eigenvalues |
| MAN-15 | [#40](https://github.com/patrickdugan/OntologicalProofs/pull/40) | Trace of a finite endomorphism commutator vanishes; square support with three edges forces two branching vertices |
| MAN-16 | [#41](https://github.com/patrickdugan/OntologicalProofs/pull/41) | Composition of nonzero linear maps through the complex scalar fibre cannot vanish |
| MAN-17 | [#42](https://github.com/patrickdugan/OntologicalProofs/pull/42) | Five-dimensional joint signed-extremal matrix normal form has zero cross-products |
| MAN-18 | [#43](https://github.com/patrickdugan/OntologicalProofs/pull/43) | Extend four orthonormal eigenvectors to a five-dimensional basis and transport the matrix proof |
| MAN-19 | [#44](https://github.com/patrickdugan/OntologicalProofs/pull/44) | Signed unit eigenvectors are orthonormal in the two directions |
| MAN-20 | [#45](https://github.com/patrickdugan/OntologicalProofs/pull/45) | Selfadjoint norm-one finite-dimensional operator has a nonzero eigenvector at `+1` or `−1` |
| MAN-21 | [#46](https://github.com/patrickdugan/OntologicalProofs/pull/46) | With the contraction bounds, zero trace, norm one and grading involutions, `AB=BA=0` in complex dimension five |
| MAN-22 | [#47](https://github.com/patrickdugan/OntologicalProofs/pull/47) | Eight exact `5×5` product entries for coordinate commutators in canonical fibre multiplicity `(2,1,1,1)` |
| MAN-23 | [#48](https://github.com/patrickdugan/OntologicalProofs/pull/48) | Hermiticity and zero products eliminate opposite-corner couplings and exclude singleton branching |
| MAN-24 | [#49](https://github.com/patrickdugan/OntologicalProofs/pull/49) | If both coordinate commutators are nonzero, the `11` truth fibre is isolated; its indicator commutes with `D` |
| MAN-25 | [#50](https://github.com/patrickdugan/OntologicalProofs/pull/50) | Canonical `(2,1,1,1)` pattern contradicts the explicit opposite-corner Connes dual upper bound of 2 |

All listed merged PRs passed the repository's `LTR Reconstruction` Lean
build and `#print axioms` check. Their theorem statements retain their
individual hypotheses. Check the corresponding source modules in
`Neoplatonic/LTR/`.

## Exact analytical dependency

Let `P,Q` be the diagonal two-bit coordinate projections on the
faithful finite Hilbert representation and `D=D*`. Set

`A=i[D,P]`, `B=i[D,Q]`.

Exact Hamming Connes distances are expected to supply the following
necessary hypotheses:

1. Opposite-corner distance attainment and equality along each
   two-edge Hamming geodesic produce witnesses `p+q` and `p−q`
   with `‖A+B‖≤1` and `‖A−B‖≤1`.
2. Unit adjacent distances give `‖A‖≥1` and `‖B‖≥1`.
   The preceding two contractions give the reverse inequalities.
3. Projection commutators are trace zero and anticommute with
   `2P−1` and `2Q−1`. In dimension five, MAN-21 concludes `AB=BA=0`.
4. For the canonical multiplicity pattern `(2,1,1,1)`, MAN-22 through
   MAN-24 show the `11` sector is isolated. The observable taking value
   3 at `11` and 0 at the other truth sectors has zero commutator.
5. MAN-25 checks the contradiction with the required dual bound
   `|f(00)−f(11)|≤2`.

The operator-norm contraction hypotheses in step 1 and the exact dual
bound in step 5 are formulated as premises in the relevant Lean theorems.
The written metric argument supplies them; their connection to one
universal `ConnesDistance` definition awaits a final integrated theorem.

## Explicit remaining Lean obligations

**G1: exact metric to norm witnesses.** Formalize compactness of the
finite-dimensional seminorm unit ball modulo constants, attainment of
both opposite-corner dual suprema, complex phase normalization and
real-part reduction, then the Hamming-geodesic midpoint rigidity. Derive
the two operator norm bounds without assuming the witnesses.

**G2: representation/operator interface.** Starting from arbitrary
selfadjoint `D` and a faithful unital representation of `ℂ^4` on
`ℂ^5`, obtain four nonzero atomic projections with multiplicities
`(2,1,1,1)` in some order. Transport MAN-21's continuous-operator
hypotheses to the coordinate matrices in MAN-22 and MAN-25.

**G3: all duplicated truth vertices.** The four multiplicity patterns
are related by bit-flip automorphisms of the square. Certify permutation
invariance of the Dirac commutator products and dual metric and carry the
canonical `00`-doubled contradiction across every pattern.

**G4: dimensions four and below.** Complete the earlier four-dimensional
Lean matrix certificate, or use a rank/compression argument with a
dimension-`≤5` extension of the spectral normal form. Faithfulness
already forces dimension at least four.

**G5: universal wrapper.** State and kernel-check a final theorem that
every faithful finite spectral triple realizing exact Hamming distance
on the two-bit Boolean square has complex Hilbert dimension at least
six, using G1–G4 and the verified eight-dimensional edge-block upper
construction.

The currently kernel-verified eight-dimensional construction establishes
`r_geom(2)≤8`. The written lower bound is `r_geom(2)≥6`; the
universal Lean theorem remains open. Numerical searches in six and
seven dimensions do not certify realizability or optimality.
