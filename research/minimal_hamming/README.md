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
~~~

The smoke test evaluates the four independent two-point Dirac blocks whose
eight-coordinate spectral metric is exactly Hamming. The target ordered
pair distances are \((1,1,1,1,2,2)\). The smoke run checks agreement
within \(10^{-4}\), and prints measured numerical error.

For each six/seven-dimensional multiplicity representative, the script
forms a real-symmetric Dirac matrix with all cross-atom couplings
variable. It fixes \(f(0)=0\) and numerically computes six support
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
matrix itself to real-symmetric matrices, a genuine limitation.

### Interpreting search output

The scale-invariant L2 and Linf errors compare the computed distances
with their Hamming targets after the best common rescaling. A small
value suggests a construction worth examining with higher-accuracy
semidefinite solvers and exact algebraic certification. A positive
value from a finite optimization search establishes no dimension
lower bound.

Future work: include complex Hermitian Dirac parameters, certified
interval or SDP bounds, and a Lean proof for each remaining six- and
seven-dimensional multiplicity pattern if no exact construction emerges.
