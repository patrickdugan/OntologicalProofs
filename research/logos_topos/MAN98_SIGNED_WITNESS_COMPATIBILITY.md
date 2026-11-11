# MAN-98: signed-witness compatibility at the six-dimensional Hamming saturation frontier

Status: **research derivation and finite diagnostic**. The independent U(2) row-energy lemma is submitted in Lean. The required unitary-chart transport and coordinate-commutator operator-norm statements remain proof obligations.

## Inputs already in main

- MAN-91: for exact two-bit Hamming distances with saturated 00/11 energy `e03=1/4, e12=0`, the true Hermitian witness `W+ = A+B` satisfies `W+²=I₆`.
- MAN-94: with the neutral projector `Q`, the corner `X=CW+C` is tripotent of rank two and the neutral-to-corner map `Y=CW+Q` is isometric on the neutral sector.
- MAN-95: the surviving original opposite Dirac block `D03` has rank one, including the 2+2 corner multiplicity.
- MAN-96: `4D03 D03ᴴ` is an idempotent of trace one, giving the unique nonzero singular value `1/2`.
- MAN-97: `X²` and `YYᴴ` are orthogonal rank-two projections spanning the four-dimensional corner.

These statements are conditional on exact Hamming realization and the specified *individual* opposite-block energies.

## Canonical opposite-double model

Consider multiplicities `(m0,m1,m2,m3)=(2,1,1,2)`. Choose orthonormal bases `(p0,q0)` on truth atom 0 and `(p3,q3)` on truth atom 3 so that `p0,p3` span the rank-one opposite channel `X`, with `q0,q3` spanning its kernel. Write `n1,n2` for the singleton neutral truth fibres.

The active `p0,p3` block of `W+=A+B` is a Hermitian 2-by-2 involution with off-diagonal coefficient of unit modulus. The `q0,q3` to `n1,n2` block is a matrix `U ∈ U(2)` by MAN-94/97.

For the other signed witness `W-=A-B`, the two-bit Boolean commutator coefficients change the four adjacent entries of that block by the sign table

```text
                n1   n2
    q0          -1   +1
    q3          +1   -1
```

The corner opposite coupling contributes to `W+` and vanishes in `W-`; the neutral opposite block vanishes because `e12=0`.

Consequently, using `U=(u_ij)`, the coordinate commutators split into an active 2-dimensional part with eigenvalues `±1/2` and a complementary 4-dimensional part. Their neutral/corner off-diagonal blocks are

```text
A : [ 0     u12 ]       B : [ u11    0  ]
    [ u21    0  ]           [ 0     u22 ]
```

so

```text
||A|| = max(1/2, |u12|, |u21|)
||B|| = max(1/2, |u11|, |u22|)
```

For `U∈U(2)`, `|u11|=|u22|`, `|u12|=|u21|`, and

```text
|u11|² + |u12|² = 1.
```

Thus

```text
min(||A||, ||B||) ≤ 1/√2.
```

**Candidate contradiction.** The original exact-Hamming metric requires `||A||≥1` and `||B||≥1`. For example, if `||A||<1`, scaling the first-coordinate bit function to a unit-admissible Dirac commutator produces a difference strictly larger than 1 across a corresponding Hamming edge. This would contradict the exact edge distance. The same argument applies to `B`.

The remaining formal work is to transport the canonical bases into the *actual* six-coordinate Dirac chart, prove that the other signed witness has the stated sign table on this invariant decomposition, and establish the two operator-norm identities. MAN-98's standalone Lean row-energy lemma proves the final scalar obstruction, but the full metric no-go remains unverified.

## Triple-corner patterns

For `(m0,m1,m2,m3)=(1,1,1,3)`, the saturated opposite block consumes the entire one-dimensional fibre of atom 0. The kernel of `X` in the corner lies within the two unused directions of atom 3, and `XY=0` forces the 0-to-neutral adjacent commutator blocks to vanish.

The tentative separating Lipschitz function is

```text
f(00)=0,  f(01)=3,  f(10)=3,  f(11)=2.
```

Its proposed commutator norm is 1: the active 00/11 component has weight `2×1/2=1`; the two adjacent components form an orthogonal unitary block in the unused atom-3 fibre. This would give `d(00,01)≥3`, inconsistent with the desired Hamming edge distance 1. The `(3,1,1,1)` case is symmetric with atom 3 singleton. Both calculations need explicit Hilbert operator-norm certificates.

## Scope of the potential theorem

The argument targets the *pure* positive/negative saturation patterns `e03=1/4,e12=0` and `e03=0,e12=1/4`. Maximal *difference* `|e03-e12|=1/4` can involve nonzero energy on both opposite diagonals when a pair has minimum fibre multiplicity two. That case requires additional analysis before any general strict-overlap conclusion.

No existence or nonexistence theorem is asserted for all faithful six-dimensional exact-Hamming representations.

## Verification

The accompanying script `man98_signed_witness_scan.py` constructs the canonical opposite-double witnesses from real rotations and generic complex Haar-unitary 2-by-2 matrices. It checks the involution, signed-witness spectral ranks, exact block norm formulas, and the numerical `1/√2` bound. Numerical scans are diagnostics, not Lean proof certificates.

## Formal targets

1. Transport the MAN-97 `im(X²) ⊕ im(YYᴴ)` splitting into orthonormal bases aligned separately with truth atoms 00 and 11.
2. Prove the Boolean sign-table conjugation of `Y` for `W-=A-B` on these bases.
3. Prove `||A||=max(1/2,|u12|)` and `||B||=max(1/2,|u11|)` in the actual complex Euclidean operator norm.
4. Derive the coordinate-bit norm lower bounds from the *definition* of the six exact Connes distances.
5. Close the opposite-double contradiction, then encode and verify the triple-corner separating function.
