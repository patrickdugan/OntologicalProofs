# GK-01: universal-ground rank-one subtraction

**Status:** candidate Lean 4.35.0 file; compile/axiom confirmation pending CI. Relies on `Neoplatonic/Arithmetic.lean` and its proven reachability theorems.

For integers `m,n >= 2`, define

```
K(m,n) = gcd(m,n)/sqrt(mn)
v(n)   = 1/sqrt(n)
R(m,n) = (gcd(m,n)-1)/sqrt(mn).
```

Then `K = vv^T + R`. This splits the contribution of divisor 1 from the remaining common-divisor structure.

The support statement in the new `Neoplatonic/GroundKernel.lean` is:

```
gcd(m,n)-1 > 0  iff  exists d>=2 with d|m and d|n
               iff  not Coprime m n.
```

`d` is an object of the original unitless grounding model, and divisibility is expressed through `Reach divPrior₂`. The rank-one identity and numerator-support equivalence are the new local proof targets. The full positive-semidefinite Gram decomposition for the remainder is a follow-up cross-toolchain port. From Gauss' identity, its matrix entries equal a sum over common nonunit divisors with weights `φ(d)/sqrt(mn)`, so the PSD argument is straightforward once the libraries align.

**External mathematical comparison:** `idolum-ai/riemann-venue` `RiemannVenue/Kernels/GCD.lean` and `RiemannVenue/Kernels/Positivity.lean` prove the totient factorization and normalized kernel PSD using Lean 4.32.0-rc1. The OntologicalProofs toolchain is Lean 4.35.0. Source references are research provenance, not imported lemmas.

**Scientific use:** a finite divisor-incidence feature dictionary supplies a planted mechanism for an observer experiment. Control for the nonunit support graph, rank-matched random Gram matrices and observation noise. Interpret grounded common-divisor support as an arithmetic property; no connection to actual metaphysical unity or RH is asserted.

Reproduce the intended new kernel claims with:

```sh
lake env lean Neoplatonic/GroundKernel.lean
```
