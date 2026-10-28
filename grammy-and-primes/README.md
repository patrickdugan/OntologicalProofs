# Grammy and Primes

A Graham-scale arithmetic experiment inside [OntologicalProofs](https://github.com/patrickdugan/OntologicalProofs), with an RH-dependent ontological argument deliberately opened for falsification.

The joke is that a prime field of roughly Graham's-number size would demand roughly log₂(G) logical qubits just to encode one field element. Graham's number is 3^E, hence composite. Factorial-wheel candidates G!k ± 1 evade every prime sieve up to G, but Euclid's trick cannot certify simultaneous primality. Over F₇[T], however, the four polynomials T^(3^m) - a with a ∈ {2,3,4,5} are irreducible for all m≥1: a rigorous four-polynomial constellation at degree G=3^E.

## What lives here

- [PrimeWheel.lean](PrimeWheel.lean) presents Lean source for H!k ± 1 avoiding every prime divisor p ≤ H and having exact gap 2. No massive numeral is evaluated.
- [RHGod.lean](RHGod.lean) formalizes conditional RH-to-God claims, the logical fallacy behind ¬RH ⇒ ¬God, an explicit propositional countermodel, and the effect of Scott modal collapse on world-indexed RH *reports*.
- [MATHEMATICAL_NOTE.md](MATHEMATICAL_NOTE.md) gives proofs, the arithmetic spectrum, the parity obstruction, and the ontology bridge audit.
- [experiment.py](experiment.py) reproduces finite primorial-wheel and Liouville-parity checks using only the Python standard library. Run python3 experiment.py.

## The live mathematical question

A hypothetical GodExists → RiemannHypothesis makes ¬RH → ¬God follow immediately. The premise is doing all the philosophical work. The repository already contains [Neoplatonic/RH.lean](../Neoplatonic/RH.lean), which marks its own SpectralAligned → commonPrior metaphysical bridge as *vacuous under RH*, along with Scott/Anderson modal results and explicit countermodels. Our new proposition-level Lean theorems cannot establish that metaphysical bridge.

A potentially more illuminating question is whether a constrained *spectral perfection* theology commits itself to RH in a way that could be falsified by finding an off-line zeta zero. That would refute the proposed spectral-perfect-being model, not every conception of God. The analogous failure mode in Gödel–Scott is that overly broad essence produces modal collapse; the existing Anderson model offers a well-defined alternative.

**The core bridge audit:** The theorem scott_spectral_bridge_iff_rh states that, under Scott's axioms on a symmetric frame, the added premise that every God-like witness implies RH is equivalent to RH itself. Thus the attractive claim that the ontological argument proves RH packages the unsolved conjecture directly into its premise.

## New spectral and Möbius investigations

- [SpectralSymmetry.lean](SpectralSymmetry.lean) gives a kernel-checkable *attempt* for a symmetric off-axis rational spectrum and shows why global symmetry alone does not imply pointwise RH-style alignment.
- [SPECTRAL_THEOLOGY.md](SPECTRAL_THEOLOGY.md) audits the Hilbert–Pólya, Li-positivity and Möbius-cancellation possibilities, with epistemic boundaries and falsifiers.
- [mobius_experiment.py](mobius_experiment.py) checks six independently published Mertens-function values up to x=1,000,000.
- [polynomial_experiment.py](polynomial_experiment.py) implements a finite-field Frobenius irreducibility test for the four polynomials x^(3^m)−a over F7 at m=1,2,3,4, including a reducible control. The Graham-degree generalization is proven mathematically in the research note, not by enumeration.
- [CI workflow](../.github/workflows/grammy-and-primes.yml) checks the three Lean files and runs both Python scripts. GitHub Actions compilation status must be read from the current PR checks before describing these files as verified.


## Evidence labels

- **Lean, source awaiting compile check:** Written for Lean v4.35.0/mathlib v4.35.0. Run lake env lean grammy-and-primes/PrimeWheel.lean and lake env lean grammy-and-primes/RHGod.lean. Do not describe these as compiler-verified until those commands succeed.
- **Proved by mathematical argument:** CRT wheel correlation, its finite Fourier identity, and the F₇[T] binomial irreducibility argument.
- **Experiment:** The Python routine tests finite cases, using a deterministic Miller–Rabin algorithm valid strictly below 2^64. Its checked results do not prove infinite prime distribution.
- **Conjecture:** Hardy–Littlewood twin-prime asymptotics, RH, and the spectral-zero-correlation inversion heuristics.
- **Metaphysical premise:** GodExists → RH and any claim from arithmetic symmetry to an ontological first principle. Each requires independent justification.

## Run

From the repository root:

    python3 grammy-and-primes/experiment.py
    python3 grammy-and-primes/mobius_experiment.py
    python3 grammy-and-primes/polynomial_experiment.py
    lake build Neoplatonic
    lake env lean grammy-and-primes/PrimeWheel.lean
    lake env lean grammy-and-primes/RHGod.lean
    lake env lean grammy-and-primes/SpectralSymmetry.lean

Keep the epistemic distinction visible when extending this folder: an explicit condition under which a claim follows is useful; naming a condition after a deity does not independently show that it holds.
