# MAN-119 | Actual six-dimensional neutral half-energy

**Status:** Original-coordinate transition half-energy theorem compiled on the stacked branch; rebased onto main for final check. This module imports the kernel-verified Gram positivity theorem (MAN-118) and the genuine two-by-two transition trace table (MAN-117).

Define the positive saturated witness W=A+B, its neutral projector Q and corner C=I-Q, and Y=CWQ. Write P0 for the truth-atom 00 projector and N1,N2 for the singleton neutral truth atoms.

The two transition values are
```
a = Tr(P0 Y N1 Yᴴ)
b = Tr(P0 Y N2 Yᴴ).
```

MAN-118 realizes a,b as real nonnegative Frobenius energies of the matrices P0YN1 and P0YN2. MAN-117 identifies their row sum exactly. Hence

```
a ≥ 0, b ≥ 0, a + b = 1,
a ≤ 1/2 or b ≤ 1/2.
```

All matrices are the actual six-dimensional labelled Dirac operators. The conclusion does not select a U(2) basis.

The remaining operator-norm lemma is a separate statement: transport the coordinate commutator squares into mutually orthogonal Hermitian channels; bound the relevant channel by its transition energy; combine with the saturated 1/2 opposite channel to show at least one of the two coordinate commutators has norm strictly less than one. Exact Hamming distances force each coordinate norm at least one, giving the intended contradiction. This norm bridge is under independent development in the MAN-120 direction.

The proof tracks all assumptions: faithful labels, Hermitian Dirac matrix, exact two-bit Hamming Connes distances and pure positive opposite saturation e03=1/4,e12=0. No statement about broader non-pure extremizers follows.
