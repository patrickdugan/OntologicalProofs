# The Logos as an arithmetic quasicrystal

Research proposal, 2026-10-28. Part of [Grammy and Primes](../README.md).

The proposed ontology says that God grounds a Logos, or Prime Intellect, whose mathematical realization has quasicrystalline order. This note asks which properties of that realization would force the Riemann hypothesis. A precise route uses continuity of a signed arithmetic distribution on Schwartz space. The accompanying Lean file verifies a complementary route through real eigenvalues and a correspondence covering every nontrivial zeta zero.

The analytic criterion below is a theorem in the cited literature. The proposed account of divine creation supplies additional premises. Its mathematical construction remains an open task.

## 1. Give the proposed Logos a mathematical role

Here, creation means ontological dependence. Let `Creates(g,L)` say that a source `g` grounds an intelligible structure `L`. This interpretation belongs to this research model; it makes no claim about agreement among religious traditions.

Assign `L` an arithmetic realization `T_L`. The proposed argument needs these commitments:

| Commitment | Content | Current status |
|---|---|---|
| Ontological origin | Divine existence supplies a Logos `L` | Proposed metaphysical premise |
| Analytic regularity | The construction of `L` yields a tempered distribution `T_L` | Mathematical obligation for the construction |
| Arithmetic fidelity | On every compactly supported smooth test, `T_L` equals the specific prime distribution below | Arithmetic identification obligation |
| Analytic implication | Temperedness of that prime distribution implies RH | Arias de Reyna's Theorem 3 [R2] |

These commitments imply

\[
\mathsf{GodExists}\Longrightarrow RH.
\]

An independently defined construction could make this a substantive research program. Giving a name to the entire implication leaves its justification outstanding. The useful question is why an account of the Prime Intellect would enforce the specified arithmetic fidelity and analytic regularity.

The model can describe the Logos as containing relations among all positive integers, with multiplicative composition represented by addition of frequencies. This suggests `log(ab)=log a+log b`. Unique factorization gives the prime directions a precise role. The weights and convergence estimates still require their own derivations.

## 2. Dyson's proposal and the meaning of quasicrystal

Freeman Dyson proposed approaching RH by classifying one-dimensional quasicrystals and identifying a structure associated with zeta zeros in *Birds and Frogs* (2009) [R1]. Subsequent work makes the definitions and correction terms essential. Kurasov and Sarnak explicitly discuss the limits of treating the prime explicit formula as an ordinary Fourier quasicrystal [R4].

Several mathematical objects enter this subject:

| Object | Operation that produces its spectrum | Requirement for this project |
|---|---|---|
| A point configuration modelling a quasicrystal | Fourier transform of its volume-averaged autocorrelation | An exact connection between diffraction and arithmetic |
| A crystalline measure | Distributional Fourier transform of the measure itself | Specified atoms, coefficients, and growth conditions |
| The centered arithmetic distribution below | Fourier transform with continuous background terms included | Cancellation on the full Schwartz test space |
| An operator on an inner-product space | Eigenvalues, or a suitably defined operator spectrum | Complete identification of the relevant complex zeta coordinates |

Diffraction uses an autocorrelation [R5]. Its positivity therefore has a different mathematical origin from the real-eigenvalue result in the Lean module. A proposed model must specify which operation connects its geometry to arithmetic.

## 3. A concrete RH-equivalent arithmetic object

Write `Lambda(n)` for the von Mangoldt function: it is `log p` when `n=p^m`, with `p` prime and `m>=1`, and zero otherwise. All logarithms here are natural. Define, initially on compactly supported smooth test functions,

\[
\mu_{\rm arith}
=2\cosh(x/2)\,dx
-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
  \left(\delta_{\log n}+\delta_{-\log n}\right).
\]

Arias de Reyna proves in Theorem 3 of [R2] that

\[
RH\quad\Longleftrightarrow\quad
\mu_{\rm arith}\text{ extends continuously to }\mathcal S(\mathbb R).
\]

The space `S(R)` consists of smooth functions whose derivatives decay faster than every reciprocal polynomial. A tempered distribution is a continuous linear functional on this space. Continuity can be expressed by a bound

\[
|T(\phi)|\le C\sum_{j=0}^{N}
\sup_x(1+|x|)^N|\phi^{(j)}(x)|
\]

for fixed `C,N` and every Schwartz test `phi`.

Under RH, the same paper obtains the Fourier identity

\[
\mathcal F\left(
\sum_{\gamma}\delta_{\gamma/(2\pi)}
-2\vartheta'(2\pi t)\,dt
\right)=\mu_{\rm arith},
\qquad
\widehat f(x)=\int_{\mathbb R}f(t)e^{-2\pi itx}\,dt.
\]

The ordinates `gamma` run through all nontrivial zeros, with multiplicity. The phase is the Riemann--Siegel theta function. The continuous terms are part of the equality. This is the generalized, centered interpretation of quasicrystalline order used for the proposal.

### How cancellation controls the distribution

The following derivation explains the criterion with the sign convention above. For `u>0`, the cumulative signed mass is

\[
A(u)=\mu_{\rm arith}((0,u])
=4\sinh(u/2)
-\sum_{n\le e^u}\frac{\Lambda(n)}{\sqrt n}.
\]

Starting from the classical RH estimate

\[
\psi(X)=X+O(\sqrt X\log^2X),
\]

partial summation gives

\[
\sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}
=\frac{\psi(X)}{\sqrt X}
+\frac12\int_1^X\frac{\psi(t)}{t^{3/2}}\,dt
=2\sqrt X+O((1+\log X)^3).
\]

It follows that `A(u)=O((1+u)^3)`. Extend the cumulative function to negative arguments with the corresponding odd convention; point values at jumps do not affect its distributional derivative. Integration by parts gives

\[
\langle\mu_{\rm arith},\phi\rangle
=-\int_{\mathbb R}A(u)\phi'(u)\,du.
\]

The polynomial bound on `A` makes this a continuous Schwartz functional. For example, a constant multiple of `sup_u (1+|u|)^5 |phi'(u)|` bounds the integral.

Absolute mass has different growth. The continuous and atomic components are mutually singular, so their contributions add in total variation. Their combined variation on `[-u,u]` grows asymptotically as `8 exp(u/2)`. The required control is cancellation against smooth tests. Meyer gives elementary examples of signed tempered measures with exponentially growing variation [R3].

The displayed expression for `A` follows directly from the definition of `mu_arith`. The cumulative-function display in [R2] has the opposite sign; the polynomial growth argument is unaffected. Computations in this folder use the sign displayed here.

### Why the condition excludes off-line zeros

Here is a Laplace-transform derivation of the converse, included as an explanation of the cited theorem. Let `mu_+` be the restriction to the positive half-line. Temperedness of `mu_arith` implies temperedness of this restriction: a smooth cutoff with transition inside `(0,log 2)` leaves only a compactly supported finite measure with bounded density. There are no prime atoms in that transition interval.

A tempered distribution supported in `[0,infinity)` has a holomorphic Laplace transform on `Re(s)>0`. Fix one smooth cutoff `eta` equal to one on a neighborhood of `[0,infinity)` and zero sufficiently far to the left. The test `eta(x) exp(-sx)` depends holomorphically on `s` as a Schwartz function in that half-plane. For `Re(s)>1/2`, absolute convergence gives

\[
\begin{aligned}
F(s)
&=\int_0^\infty2\cosh(x/2)e^{-sx}\,dx
-\sum_{n\ge2}\frac{\Lambda(n)}{n^{s+1/2}}\\
&=\frac1{s-1/2}+\frac1{s+1/2}
+\frac{\zeta'(s+1/2)}{\zeta(s+1/2)}.
\end{aligned}
\]

At `s=1/2`, the contribution from the pole of zeta cancels the first rational term. Any zeta zero `rho` with `Re(rho)>1/2` would create an uncancelled pole at `s=rho-1/2`. Holomorphy on `Re(s)>0` excludes those zeros. The functional equation supplies the corresponding conclusion on the other side of the critical line.

This derivation concerns complex analysis of the specified distribution. It has not been formalized in the Lean file.

## 4. A finite-rank obstruction for literal cut-and-project models

Suppose all nonzero atomic frequencies belong to an additive subgroup `Gamma` of the real line with finite rational rank `r`. This includes

\[
\Gamma=\mathbb Z\omega_1+\cdots+\mathbb Z\omega_r.
\]

Then `Gamma` contains `log p` for at most `r` distinct primes `p`.

**Proof.** Distinct prime logarithms are linearly independent over the rationals. A finite rational relation can be cleared of denominators to give

\[
\sum_{j=1}^m a_j\log p_j=0,\qquad a_j\in\mathbb Z.
\]

Exponentiating and moving negative exponents to the other side gives an equality between products of distinct primes with nonnegative integer exponents. Unique factorization forces every `a_j=0`. The rational span of `Gamma` has dimension `r`, so it contains at most `r` members of this independent family. QED.

This applies to the Fourier module of a regular Euclidean cut-and-project model obtained from a lattice in `R^(1+m)`: its Bragg frequencies lie in the projection of the dual lattice, a module of rank at most `1+m` [R5, R6]. It also applies to the finite frequency generators in the Kurasov--Sarnak construction [R4]. The statement concerns locations of nonzero atoms. Such a module can be dense, so taking its topological closure would discard the relevant information.

Adding a nonatomic background preserves the obstruction. At the singleton `{log p}`, the arithmetic measure has mass `-log(p)/sqrt(p)`, while a background density contributes zero. Exact matching therefore demands each prime frequency. The sign of an atomic coefficient has no effect on this argument; physical diffraction would additionally require nonnegative intensities.

### Graham's number reappears as an exact rank bound

Capturing every prime frequency through a cutoff `H` requires

\[
\dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}\Gamma\ge\pi(H),
\]

where `pi(H)` counts primes at most `H`. For a one-dimensional Euclidean cut-and-project scheme with `m` internal dimensions,

\[
1+m\ge\pi(H).
\]

Setting `H=G`, Graham's number, yields the symbolic requirement `1+m>=pi(G)` for this exact finite-cutoff representation. This concerns the mathematical construction's frequency rank.

The full arithmetic module is

\[
\Gamma_{\rm arith}
=\bigoplus_{p\text{ prime}}\mathbb Z\log p
=\log(\mathbb Q_{>0}).
\]

It has infinite rational rank and still lies inside the one-dimensional real line. A generalized model could use this module or another specified representation. Merely allowing infinitely many integer generators is insufficient: `Z[1/2]` has rational rank one. The arithmetic requirement is infinite rational rank.

A compact rule can define the entire module. The earlier Graham-scale theme therefore returns through the difference between the length of a definition and the size or rank of its mathematical realization.

## 5. The complete spectral coordinate

For `rho=beta+i gamma`, define

\[
E_\rho=-i(\rho-1/2)=\gamma+i(1/2-\beta).
\]

Then `E_rho` is real exactly when `beta=1/2`. The Lean module proves this identity and uses the genuine Mathlib `RiemannHypothesis` to obtain

\[
RH\Longleftrightarrow
\forall\rho\text{ nontrivial zero},\quad E_\rho\in\mathbb R.
\]

Its operator theorem states that a complex linear map symmetric for an inner product, with every `E_rho` among its eigenvalues, forces RH. The implication uses Mathlib's `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`. Symmetry suffices for this eigenvector argument. An unbounded operator on a completed Hilbert space needs a domain and spectral correspondence of its own. The Lean theorem allows an incomplete inner-product space, such as a suitable invariant domain; it does not construct that domain.

`SpectralLogos` records an operator, a proof of its symmetry, and complete arithmetic coverage. Its existence is a premise in the creation theorem. Quasicrystal structure remains an additional construction problem for a proposed instance.

### An exact projection control

Consider these synthetic multisets, retaining every multiplicity:

\[
Z_{\rm on}=\{1/2+i,1/2-i,1/2+i,1/2-i\},
\]

\[
Z_{\rm off}=\{1/3+i,1/3-i,2/3+i,2/3-i\}.
\]

Both preserve conjugation and reflection around the critical line. Projection onto the imaginary coordinate gives the same counting measure `2 delta_-1 + 2 delta_1`. Their finite autocorrelations have coefficients `(4,8,4)` at `(-2,0,2)`. The normalized intensity in both cases is

\[
I(k)=\left|\frac14\sum_\gamma e^{-2\pi ik\gamma}\right|^2
=\cos^2(2\pi k)
\]

for every real frequency. The coordinate `E_rho` distinguishes the configurations. This is a finite algebraic control about information retained by a projection. The examples assert no zeta zeros, and their finite intensity is not a thermodynamic diffraction calculation.

## 6. A concrete construction target

Choose an even smooth cutoff `chi` equal to one on `[-1,1]` and zero outside `[-2,2]`. Set

\[
\mu_R=\chi(x/R)\mu_{\rm arith},\qquad R\ge1.
\]

Each finite truncation defines a tempered distribution. The target is one fixed pair `C,N` for which

\[
|\langle\mu_R,\phi\rangle|
\le C\sum_{j=0}^N\sup_x(1+|x|)^N|\phi^{(j)}(x)|
\]

holds for every `R>=1` and every Schwartz function `phi`.

This uniform estimate would imply RH. For a compactly supported test, `mu_R` agrees with `mu_arith` once `R` is large enough. The estimate bounds the compact-test functional by Schwartz seminorms, giving its continuous extension by density. Apply the analytic criterion.

Conversely, temperedness gives a uniform estimate because multiplication by `chi(x/R)` has uniformly bounded action on each required Schwartz seminorm for `R>=1`. This is an elementary functional-analytic reformulation of the target.

The task for a quasicrystal model is to derive this estimate through independently controlled approximants and prove exact arithmetic matching. A growing collection of finite positive matrices, bounded numerical residuals, or larger cutoff values establishes the corresponding finite statements.

## 7. Consequences for the ontological proposal

Write `B` for the substantive assertion that divine existence supplies a Logos with the required arithmetic realization. The argument has the form

\[
B\Longrightarrow(\mathsf{GodExists}\Longrightarrow RH).
\]

A counterexample to RH would give `not(B and GodExists)`. Retaining divine existence as a premise would reject `B`. Keeping `B` would let contraposition reject that formulation of divine existence. The choice concerns the joint theory being tested.

The explanatory question is whether an account of intelligibility can independently select the arithmetic representation and require its uniform regularity. The prime-frequency obstruction gives that account a concrete demand: a fixed finite-rank construction cannot realize the stated distribution. The analytic criterion specifies the cancellation that an admissible generalized construction must prove.

## 8. Verification ledger

| Claim | Evidence in this folder |
|---|---|
| Rotated-coordinate formulas and two equivalences with actual RH | Lean proofs |
| Symmetric operator plus complete zero coverage implies RH | Lean proof using Mathlib eigenvalue reality |
| Conditional creation implication and failure audit | Lean proofs with explicit premises |
| Equal projected finite intensities for synthetic configurations | Exact rational Python control and displayed derivation |
| Centered prime mass through one million | Floating-point calculations with `math.fsum` and elementary controls |
| Obstruction from a finite-rank frequency module | Written proof using unique factorization |
| Tempered-distribution criterion and corrected Fourier identity | External theorem [R2] |
| Laplace explanation and uniform-cutoff reformulation | Written analytic arguments in this note |
| A quasicrystalline Logos with the required arithmetic realization | Open construction and metaphysical premise |

All eleven exported Lean theorems print their axiom dependencies. Local compilation used Lean 4.35.0 and pinned Mathlib 4.35.0. The Python output is reproduced in [results.json](results.json). The workflow compiles Lean scripts recursively, including this subfolder.

## Sources

[R1] Freeman Dyson, *Birds and Frogs*, Notices of the AMS 56(2), 2009, 212--223, especially pp. 214--215. [AMS](https://www.ams.org/notices/200902/rtx090200212p.pdf), [academic mirror](https://wucj.lab.westlake.edu.cn/Others/Dyson_Birds_and_Frogs.pdf).

[R2] J. Arias de Reyna, *Explicit formula and quasicrystal definition*, arXiv:2402.10604v2, revision 13 March 2025. Theorem 3 and its Fourier convention. [Versioned record](https://arxiv.org/abs/2402.10604v2), [full text](https://arxiv.org/html/2402.10604v2).

[R3] Yves Meyer, *Measures with locally finite support and spectrum*, PNAS 113(12), 2016, 3152--3158. Definitions and examples of tempered signed measures. [Full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC4812708/).

[R4] Pavel Kurasov and Peter Sarnak, *Stable polynomials and crystalline measures*, Journal of Mathematical Physics 61, 083501 (2020). Definitions and finite generators in equations (13)--(14). [arXiv](https://arxiv.org/abs/2004.05678), [author manuscript](https://staff.math.su.se/kurasov/PDFARCHIV/2020-KuSa1-arXiv.pdf).

[R5] Michael Baake and Uwe Grimm, *Mathematical diffraction of aperiodic structures*, Chemical Society Reviews 41 (2012), 6821--6843. Autocorrelation, regular model sets, and Fourier modules. [arXiv](https://arxiv.org/abs/1205.3633), [publisher](https://doi.org/10.1039/C2CS35120J).

[R6] Uwe Grimm, *Aperiodic crystals and beyond*, Acta Crystallographica B 71 (2015), 258--274. Fourier-module rank in the discussion of equations (12)--(13). [Full text](https://journals.iucr.org/b/issues/2015/03/00/dq5011/).

Related repository work: [positivity bridge](../POSITIVITY_BRIDGE.md), [divisor-to-Weil investigation](../DIVISOR_TO_WEIL.md), and [earlier spectral theology](../SPECTRAL_THEOLOGY.md). This proposal adds a distributional regularity criterion and a finite-rank obstruction to those investigations.
