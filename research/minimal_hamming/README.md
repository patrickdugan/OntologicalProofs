# Minimal two-bit Hamming Connes dimension

## Verified baseline

The formal Lean developments in Neoplatonic/LTR establish:

- **MAN-53:** No faithful unital complex star-algebra representation of
  \(\mathbb C^4\) on \(\mathbb C^5\), with Hermitian Dirac matrix,
  produces all six exact two-bit Hamming distances.
- **MAN-09 / MAN-54:** The finite Boolean-cube edge-Dirac construction
  produces exactly the Hamming Connes dual supremum. For the two-bit square,
  the four distinct edges contribute two complex Hilbert coordinates each,
  giving a concrete **eight-coordinate realization**.

A faithful four-dimensional representation attaining Hamming would embed
in a five-dimensional faithful representation by adjoining a duplicate
one-dimensional truth character and a decoupled Dirac component. The
Connes seminorm and all pure-state distances would be unchanged.
Dimensions below four cannot faithfully represent all four atomic
truth characters. Thus the current mathematical bounds are

\[
6 \leq d_{\min} \leq 8.
\]

The classification and existence question at dimensions six and seven
remains open in this formal development. Numerical fits cannot settle it.

## Six-dimensional formal progress (2026-11-11)

The original-coordinate six-dimensional formalization has advanced well
past fibre enumeration. All results below concern a **faithful** diagonal
representation of the four truth atoms, with one Hermitian complex
six-dimensional Dirac matrix and all six Connes distances exactly
equal to the two-bit Hamming metric.

- **MAN-109 through MAN-112:** singleton opposite truth fibres are excluded
  under pure positive saturation, leaving the (2,1,1,2) multiplicity pattern.
  Boolean-square translation mirrors this classification for pure negative
  saturation.
- **MAN-123 through MAN-135:** the actual labelled Dirac coordinate
  commutators admit orthogonal signed-channel decompositions. A bistochastic
  energy trace and the true complex Hilbert C*-operator norm prove that
  pure saturation (E03,E12)=(1/4,0) is impossible. This removes the
  remaining opposite-double saturated candidate without choosing a
  hypothetical canonical U(2) basis.
- **MAN-136:** the mirrored (E03,E12)=(0,1/4) configuration is impossible.
- **MAN-137 and MAN-138:** even maximal *non-pure* residual Pauli
  overlap is excluded. The universal necessary inequality is strict:
  
  \[
  |E_{03}-E_{12}|<\frac14,\qquad |c|<\frac12,\qquad
  c=2(E_{03}-E_{12}).
  \]
  
  Here E03 and E12 are oriented squared Dirac block energies.
  This theorem excludes both endpoints of the sharp Pauli overlap
  region. It does not exclude the strict interior.
- **MAN-139, MAN-141, MAN-142:** quantitative real Pauli Gram
  estimates for near-endpoint witnesses are proved, including
  \( |q+r-\tfrac12|\le\varepsilon \),
  \( (q-r)^2\le 2\varepsilon \), and bounds on one signed
  residual quadratic energy and the complementary spectral defect.
- **MAN-140:** the nonsaturated signed witness W=A+B is governed by
  an exact spectral defect \(\Delta=I-W^2\).
  For neutral projector Q, C=I-Q, X=CWC, and Y=CWQ, the original
  complex six-coordinate equations are
  
  \[
  X^2+YY^\dagger=C-C\Delta C,\quad
  XY=-C\Delta Q,\quad
  Y^\dagger Y=Q-Q\Delta Q.
  \]

  This is the relevant replacement for the saturated MAN-94
  partial-isometry equations.

**Remaining six-dimensional question:** determine whether the strict
interior Pauli region can satisfy all six exact Connes-Hamming
distances. The present formal lower bound on minimal dimension
remains six, and the verified eight-dimensional edge-Dirac realization
still provides the upper bound. A seven-dimensional realization or
obstruction is likewise unresolved.

## Six/seven-dimensional candidate space

For a faithful diagonal representation, the multiplicity of each atom is
a positive integer, and the four multiplicities sum to the Hilbert
dimension. MAN-55 enumerates all named-atom multiplicity patterns in Lean.

Up to permutation of atoms:

| Dimension | Multiplicity partitions |
| --- | --- |
| 6 | (3,1,1,1), (2,2,1,1) |
| 7 | (4,1,1,1), (3,2,1,1), (2,2,2,1) |

The numerical runner distinguishes adjacent from opposite doubled
vertices whenever their placement matters to the Boolean-square metric.

## Numerical reconnaissance

Install NumPy and SciPy, then run:

~~~sh
python research/minimal_hamming/search.py --smoke
python research/minimal_hamming/search.py --dimension 6 --seeds 3 --max-nfev 20
python research/minimal_hamming/search.py --dimension 7 --seeds 3 --max-nfev 20
python research/minimal_hamming/search.py --dimension 6 --complex-dirac --seeds 3 --max-nfev 20
~~~

The smoke test evaluates the four independent two-point Dirac blocks whose
eight-coordinate spectral metric is exactly Hamming. The target ordered
pair distances are \((1,1,1,1,2,2)\). The smoke run checks agreement
within \(10^{-4}\), and prints measured numerical error.

For each six/seven-dimensional multiplicity representative, the script
forms a real-symmetric Dirac matrix with all cross-atom couplings
variable. With --complex-dirac it searches the full Hermitian family
of inter-atom blocks, using independent real and imaginary components. It fixes \(f(0)=0\) and numerically computes six support
functions

\[
d_{D}(u,v)=\max_{f\in\mathbb R^4,\;L_D(f)\leq 1}
|f(u)-f(v)|,\qquad
L_D(f)=\|i[D,\operatorname{diag}(f\circ\ell)]\|_{\rm op}.
\]

The inner optimization is convex in \(f\), with spectral radius
constraints. The implementation uses SciPy SLSQP and checks feasibility.
The outer least-squares search adjusts the Dirac entries and removes
the overall metric scale before comparing the six distances.

### Why real observables suffice for a fixed Hermitian Dirac matrix

For a complex observable \(f\) and a pair \(u,v\), multiply \(f\) by a
unit complex scalar so that \(f(u)-f(v)\) is real and nonnegative, then
take its real part \(g\). The endpoint difference is preserved.
Since \(D=D^*\) and the representation is a star-homomorphism,

\[
[D,\pi(g)]
=\tfrac12\bigl([D,\pi(f)]-[D,\pi(f)]^*\bigr),
\quad
\|[D,\pi(g)]\|\leq\|[D,\pi(f)]\|.
\]

Consequently the complex and real observable suprema agree for any
fixed Hermitian \(D\). The numerical search here restricts the Dirac
matrix itself to real-symmetric matrices unless --complex-dirac is selected.
The enlarged search covers complex Hermitian cross-fibre couplings, including
nontrivial loop phases. Neither mode gives certified lower bounds.

### Interpreting search output

The scale-invariant L2 and Linf errors compare the computed distances
with their Hamming targets after the best common rescaling. A small
value suggests a construction worth examining with higher-accuracy
semidefinite solvers and exact algebraic certification. A positive
value from a finite optimization search establishes no dimension
lower bound.

Future work: certified interval or SDP bounds, with exact algebraic
certificates and Lean proofs for the remaining six- and seven-dimensional
multiplicity patterns if no exact construction emerges.
