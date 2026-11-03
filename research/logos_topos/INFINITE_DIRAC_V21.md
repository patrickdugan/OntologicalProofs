# LTR v0.21: A compact complex spectral triple on a first-order Stone completion space

**Date:** November 3, 2026

## Verification record

The complete construction has passed the Lean kernel build, explicit axiom
audit, and finite regression suite.

- [Logical Stone triple audit, run 41662893418](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41662893418)
- [Logical dense completion sequence, run 41660334629](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41660334629)
- [Explicit dense-pair marking, run 41658618727](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41658618727)
- [Positive-exponent scalar spectral series, run 41659166947](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41659166947)
- [Compact complex spectral-triple foundation, run 41644762120](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41644762120)

## Formal theorem

Let T be a satisfiable first-order theory, let α be a variable type,
and assume the expanded sentence type is countable. Suppose that there
exists a sentence φ independent of T.

Mathlib's actual complete-type space

\[
X=T.\mathrm{CompleteType}(\alpha)
\]

is compact and totally separated. The sentence-truth loci form a
clopen basis. Countability of the sentence type makes X second
countable, and Urysohn metrization supplies a compatible metric d.

A classically selected sequence q:ℕ→X has dense range.
Independence of φ produces two different complete theories, so q
assumes at least two distinct values. The explicit Nat.unpair marking
enumerates every ordered pair of distinct dense-sequence values,
replacing coincident pairs by a fixed nondegenerate fallback edge.

The resulting complex spectral data are

\[
\begin{aligned}
A &= C(X,\mathbb C),\\
A_0 &= \mathrm{Lip}(X,\mathbb C),\\
H &= \ell^2(\mathbb N,\mathbb C^2),\\
\pi(f)_j &= \operatorname{diag}(f(x_j),f(y_j)),\\
D_j &=
\begin{pmatrix}
2^j&d(x_j,y_j)^{-1}\\
d(x_j,y_j)^{-1}&-2^j
\end{pmatrix}.
\end{aligned}
\]

The verified spectral-triple record establishes density of A₀ in A,
injectivity of π, dense domain and closed self-adjointness of D,
compactness and two-sided inverse identities for (D-iI)⁻¹, and bounded
domain commutators with π(f) for every f∈A₀.

The independent metric reconstruction theorem applies to the explicit
pair marking:

\[
d(x,y)=\sup_{\substack{f\in A_0\\
\lVert[D,\pi(f)]\rVert\le 1}}|f(x)-f(y)|.
\]

The supremum is attained by the complex-valued function
f(z)=d(z,y).

## Spectral-energy summability

For arbitrary real coupling values s_j and every real p>0, Lean proves

\[
\sum_{j\ge0}2(1+4^j+s_j^2)^{-p/2}<\infty.
\]

This is the summability of scalar energy contributions from the
two-dimensional blocks, using the exact block square
D_j²=(4^j+s_j²)I₂. It strongly indicates p-summability for all p>0
and a zero spectral dimension in the usual abscissa sense.

The global operator trace identity and a formal trace-class or
Schatten-class proof are separate remaining obligations. They are not
asserted by the scalar-series theorem alone.

## Proof modules

- Neoplatonic/LTR/ComplexMetricSpectralTriple.lean
- Neoplatonic/LTR/DensePairMarking.lean
- Neoplatonic/LTR/ComplexSpectralSummability.lean
- Neoplatonic/LTR/LogicalStoneMarking.lean
- Neoplatonic/LTR/LogicalStoneSpectralTriple.lean
- Neoplatonic/LTR/Check.lean

## Interpretation and effective limitations

The selected compatible metric comes from classical metrization.
It is neither a canonical metric of the unlabelled Stone topology
nor a verified metric algorithm from sentence codes.

Countability of the sentence type supplies a countable basis and
classical dense sequence. The chosen complete theories can be
noncomputable; a computable sentence numbering does not by itself
compute those points. The formal development preserves the
sentence-truth-locus labels but has not yet proved an effective
sentence-code metric, functoriality under interpretation maps, or
reconstruction of theoremhood from this particular Dirac spectrum.

The verified result is a full spectral triple on the actual logical
completion space, conditional on the displayed satisfiability,
countability and independence hypotheses.

## Reproduce

    lake build Neoplatonic.LTR.Check
    lake env lean Neoplatonic/LTR/Check.lean
    python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
