# Logos and quasicrystals

An investigation of the proposal that God grounds a quasicrystalline Logos or Prime Intellect whose arithmetic structure forces RH.

The [research note](RESEARCH_NOTE.md) develops a precise analytic route: a signed distribution built from prime powers extends to a tempered distribution exactly when RH holds, by Arias de Reyna's Theorem 3. A proposed Logos must produce that distribution with independently justified analytic control.

There is an elementary restriction on the geometry. The frequencies `log p` are rationally independent over distinct primes, so a frequency module of finite rational rank cannot contain every prime frequency. Exact coverage through a cutoff `H` requires rank at least `pi(H)`, including the symbolic case `H=G` for Graham's number.

## Files

| File | Scope |
|---|---|
| [RESEARCH_NOTE.md](RESEARCH_NOTE.md) | Analytic criterion, finite-rank obstruction, explicit theological premises, and sources |
| [LogosQuasicrystal.lean](LogosQuasicrystal.lean) | Eleven theorems about actual Mathlib RH, real spectral coordinates, symmetric operators, and the conditional creation premise |
| [experiment.py](experiment.py) | Exact synthetic projection controls and finite centered-prime calculations |
| [results.json](results.json) | Reproducible output from the experiment |

## What Lean checks

For a nontrivial zero `rho`, the coordinate `-i(rho-1/2)` is real exactly when `Re(rho)=1/2`. The main theorem derives RH from a symmetric complex linear operator whose eigenvalues cover this full coordinate of every nontrivial zero.

`SpectralLogos` packages the operator and coverage requirements. The creation theorem assumes `GodExists -> Nonempty (SpectralLogos E)` and derives `GodExists -> RiemannHypothesis`. The existence and quasicrystalline realization of this structure remain open obligations.

The operator theorem concerns eigenvectors in an inner-product space. A physical unbounded operator requires domain analysis before it can instantiate a model. The distributional theorem from the literature remains outside the Lean formalization.

## Finite controls

The experiment constructs two rational synthetic spectra with identical ordinate multiplicities. Their projected intensities agree for every frequency even though their real coordinates have different critical-line behavior. A separate computation evaluates

\[
A(\log X)=2(\sqrt X-1/\sqrt X)
-\sum_{n\le X}\Lambda(n)/\sqrt n.
\]

At `X=1,000,000`, the smooth and atomic contributions are approximately `1999.998` and `1996.906808816`, leaving `3.091191184`. These finite values establish no universal growth estimate.

## Reproduce

From the repository root, with its pinned Lean and Mathlib versions:

```sh
lake env lean grammy-and-primes/logos-quasicrystal/LogosQuasicrystal.lean
python3 grammy-and-primes/logos-quasicrystal/experiment.py
```

The eleven Lean theorems compiled locally on Lean 4.35.0 and Mathlib 4.35.0. Their printed axiom dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`. The Python command passes with the standard library. The [repository workflow](../../.github/workflows/grammy-and-primes.yml) includes this subfolder in its recursive Lean checks and runs the experiment.
