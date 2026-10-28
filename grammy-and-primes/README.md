# Grammy and Primes

Graham-scale arithmetic and RH-dependent ontology inside [OntologicalProofs](https://github.com/patrickdugan/OntologicalProofs). The formal work keeps arithmetic results separate from additional metaphysical premises.

## Current continuation: positivity with an explicit test

[POSITIVITY_BRIDGE.md](POSITIVITY_BRIDGE.md) develops the finite weighted reflection theorem: if tau is an involution and every weight is positive, its paired quadratic form is nonnegative on all vectors exactly when tau fixes every index. Every moved orbit has an explicit negative witness. The Lean countermodel satisfies Scott's axioms and the grounding theory, identifies the God-like witness with the common root, and satisfies A6, while the independent reflection form remains negative on that witness vector.

[DIVISOR_TO_WEIL.md](DIVISOR_TO_WEIL.md) constructs an unconditional positive divisor-incidence norm and describes Suzuki's published RH-equivalent norm identity as a concrete analytic target. Equality between the divisor construction and the Weil form is an open obligation in this investigation.

A logical equivalence with RH alone does not make an independently specified arithmetic criterion circular. The unrestricted proposition-bridge audits concern their stated logical signatures. The new notes qualify the earlier use of 'vacuous' accordingly.

## Lean modules

| File | Mathematical scope |
|---|---|
| [PrimeWheel.lean](PrimeWheel.lean) | Factorial-wheel gap two and exclusion of small prime factors |
| [RHGod.lean](RHGod.lean) | Actual mathlib RH, Scott positivity, conditional bridges and countermodels |
| [SpectralSymmetry.lean](SpectralSymmetry.lean) | Reflection-invariant off-axis rational toy spectrum |
| [ReflectionPositivity.lean](ReflectionPositivity.lean) | Weighted positivity criterion, separating-test premise, Gram-map implication, Scott-root A6 countermodel |
| [DivisorGram.lean](DivisorGram.lean) | Positive divisor energy, the unit-divisor feature, exact two-point energy |

The first three modules passed GitHub Actions run 26 at `3b7c5a677efde1de1a9333c03eb52e35c0b71396`. The current scoped workflow compiles every Lean file in this folder; consult the run for the current head before claiming verification of later changes. Each new positivity theorem prints its axiom dependencies. Lean v4.35.0 and mathlib v4.35.0 remain pinned by the existing project.

## Arithmetic background

Graham's number G is a power of 3. The candidates G!k +/- 1 evade every prime divisor at most G and have gap two. Their simultaneous primality is unproved. Over F7[T], the four polynomials T^(3^m)-a for a in {2,3,4,5} are irreducible for every m>=1. The research note gives the norm-and-tower-law argument, which applies symbolically to degree G.

[MATHEMATICAL_NOTE.md](MATHEMATICAL_NOTE.md) contains the CRT wheel correlation and finite Fourier identity, the Liouville parity decomposition, and the polynomial construction. [SPECTRAL_THEOLOGY.md](SPECTRAL_THEOLOGY.md) records the earlier Hilbert-Polya, Li-coefficient and Mobius-cancellation proposals. The repository's existing [Neoplatonic/RH.lean](../Neoplatonic/RH.lean) explicitly exposes its spectral-to-grounding assumption.

## Experiments

All five scripts use the Python standard library. Their outputs describe finite checks.

| Script | Checks |
|---|---|
| `experiment.py` | Exact CRT counts, seven primorial twin-pair counts, bounded Liouville identity |
| `mobius_experiment.py` | Six Mertens-function checkpoints through one million |
| `polynomial_experiment.py` | F7 binomial irreducibility at degrees 3, 9, 27, 81, with a reducible control |
| `positivity_experiment.py` | All 1,116 involutions on sizes 0 through 8, positive weights, negative witnesses, exact principal minors, restricted-test controls |
| `divisor_gram_experiment.py` | Divisor Gram matrices and Mobius inverses through size 16, exact energies |

The positivity script uses Fraction arithmetic and no actual zeta zeros. Its 3,348 weighted cases include coinciding weight schemes at small sizes. The divisor script makes no claim that its positive form equals Weil's.

## Claim boundaries

The finite arithmetic and logical theorems prove their stated implications. The infinite analytic Weil criterion is cited from published work and has not been formalized here. The general finite-field irreducibility argument is a written proof with finite computational controls. RH, the integer twin-prime conjecture, and any inference from divine existence to arithmetic positivity remain unresolved by this work.

A hypothetical GodExists -> RH permits contraposition. An RH counterexample would refute the joint theological claim containing that implication. The existing conditional logic supplies no universal refutation of every conception of God.

## Run

From the repository root:

```sh
lake build Neoplatonic
for file in grammy-and-primes/*.lean; do lake env lean "$file"; done
python3 grammy-and-primes/experiment.py
python3 grammy-and-primes/mobius_experiment.py
python3 grammy-and-primes/polynomial_experiment.py
python3 grammy-and-primes/positivity_experiment.py
python3 grammy-and-primes/divisor_gram_experiment.py
```

[The scoped workflow](../.github/workflows/grammy-and-primes.yml) checks these commands, preserves failure status across the Lean scripts, and rejects printed `sorryAx` dependencies. Mathematical review must also inspect the hypotheses of each theorem.
