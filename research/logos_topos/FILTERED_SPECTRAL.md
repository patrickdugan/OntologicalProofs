# Filtered Logos–Topos Reconstruction, v0.2

## 1. Statement and mathematical scope

Let B and C be countable Boolean algebras, equipped with increasing sequences of finite Boolean subalgebras B_n and C_n, starting with {0,1} and exhausting their algebras. One way to obtain B_n is to generate it from the first n observations in a fixed enumeration. Their Stone spaces X_B and X_C carry the corresponding dyadic first-disagreement metrics. A homomorphism alpha : B -> C induces f_alpha : X_C -> X_B by inverse image of ultrafilters.

A countable first-order theory supplies a Boolean algebra of sentences modulo equivalence over that theory. The construction applies to a finitely axiomatized theory, and also to broader countably presented theories. Genuine interpretations induce maps of sentence algebras. Arbitrary Boolean homomorphisms need not come from first-order-definable interpretations; this theorem concerns the induced sentence semantics and preserves the chosen labels.

**Filtered spectral reconstruction theorem.** For an integer c >= 0, the following conditions are equivalent:

1. alpha(B_n) is contained in C_(n+c) for every n.
2. d_B(f_alpha(x), f_alpha(y)) <= 2^c d_C(x,y) for all x,y.
3. Pullback by f_alpha sends every real unit-Lipschitz observable to an observable with Lipschitz seminorm at most 2^c.
4. In faithful spectral realizations whose Dirac commutator seminorms equal the Lipschitz seminorms, the same pullback has commutator-seminorm bound at most 2^c.

A suitable infinite spectral realization exists by the Christensen–Ivan construction discussed below. The equivalence is at the marked observable-algebra level. A canonical unitary between Hilbert-space realizations is not supplied.

The Boolean-algebra-to-marked-space step is classical Stone duality. The actual Lean development proves the exact equivalence between prefix dependence, the dyadic distance bound, and the bound on all real unit-Lipschitz observables. The infinite-dimensional analytic realization is a written proof using an established construction. The proof ledger below records these boundaries.

## 2. Logical dependence becomes geometric distortion

For a state x, let b_k(x) be its kth Boolean observation. Set

    x ~_n y  iff b_k(x)=b_k(y) for all k<n.
    d(x,y) = 0 if x=y, and 2^(-k) at their first disagreement k.

The marks separate points. The dyadic distance is an ultrametric inducing the Stone topology. Its balls satisfy the exact identity

    x ~_n y  iff d(x,y) <= 2^(-n).

A map f has delay c when x ~_(n+c) y implies f(x) ~_n f(y). To see the Boolean-algebra interpretation, the atoms of C_m are precisely the nonempty cells of the first m observations. A Boolean-valued observable is constant on those cells exactly when its clopen truth set belongs to C_m. Thus the inclusion in condition 1 is the delay condition for every target generator and hence for B_n.

For the forward metric bound, suppose x,y first differ at k and their images first differ at j. Delay c implies k <= j+c: otherwise x,y agree through j+1+c observations, forcing image agreement through j+1, a contradiction. Therefore

    d_B(f(x),f(y))/d_C(x,y) = 2^(k-j) <= 2^c.

Equal images satisfy the same bound with zero left side. Conversely, if the metric bound holds, source agreement through n+c gives source distance at most 2^(-n-c), hence target distance at most 2^(-n) and target agreement through n.

For observables, a 1-Lipschitz a satisfies

    |a(f(x))-a(f(y))| <= d_B(f(x),f(y)).

This proves the forward bound. For its converse, fix y and test the distance observable a(z)=d_B(z,f(y)). This is 1-Lipschitz and its difference between f(x) and f(y) is exactly their distance.

Lean theorem: `translationDelay_iff_observable_bound`, supported by `translationDelay_iff_distance_bound` and `prefixAgreement_iff_distance_le`. The construction uses mathlib's actual PiNat distance. Injectivity of the marking is needed only to distinguish a metric from a pseudometric; the formal inequalities hold for either.

Depth means the position in the chosen finite observation filtration. It does not mean proof length, runtime, number of axioms, or an intrinsic complexity independent of presentation.

## 3. Exact optimal constant from the depth profile

For a continuous map f between nonempty compact marked Stone spaces, define

    h_f(n) = min {m : x ~_m y implies f(x) ~_n f(y) for every x,y}.

Each value is finite: the inverse images of the finitely many target n-cylinders are clopen; compactness expresses each as a finite union of source cylinders. Take the maximum required source depth. This gives existence, not an algorithm computing the semantic minimum.

With the convention that an empty supremum is zero,

    Lip(f) = sup_{n : h_f(n)>0} 2^(h_f(n)-n).

This holds in the extended nonnegative reals; infinity is allowed.

**Proof.** Given a pair with distinct images, let j be its first output disagreement and k its first input disagreement. At n=j+1, agreement through h_f(n) would force output agreement through n. Thus k<h_f(n), and the pair's ratio 2^(k-j) is at most 2^(h_f(n)-n). This proves the upper bound. For the lower bound, let m=h_f(n)>0. Minimality supplies a pair agreeing through m-1 whose images disagree before n. The defining property at m forces this pair's first input disagreement to be exactly m-1. Its first output disagreement j is at most n-1, so its ratio is at least 2^(m-n).

The same constant is the optimal pullback bound on real unit-Lipschitz observables. Under a spectral realization L_D=Lip it is also the optimal Dirac-commutator pullback bound:

    sup_{L_D_B(a)<=1} L_D_C(a o f) = Lip(f).

The upper bound is composition of Lipschitz estimates. For the lower bound, distance-to-image observables witness every pair ratio. The exact depth-profile formula is a written theorem with exhaustive finite checks; the integer-delay equivalence and the observable test are kernel-checked.

## 4. Composition and the class of admissible interpretations

The identity has delay zero. If f has delay c and g has delay d, then g o f has delay c+d. More precisely,

    h_(g o f)(n) <= h_f(h_g(n)),
    Lip(g o f) <= Lip(g) Lip(f).

Observable pullback obeys (a o g) o f = a o (g o f) exactly. Thus bounded-delay maps form a category, with contravariant pullbacks on marked observable algebras. If an inverse has delay d, the two metrics obey both bounds and are bi-Lipschitz equivalent. Zero delay in both directions gives an isometry. The claims concern composition of observables, without an assertion that arbitrarily chosen Dirac eigenbases compose functorially.

This is a genuine restriction on interpretations. On the full binary completion space, f(x)_k=x_(2k) is computable and continuous. For n>=1 its least depth is h_f(n)=2n-1, so its Lipschitz constant is infinite. Finite initial segments exhibit the increasing constants. A map with only a computable dependence modulus need not have bounded additive delay.

An example inside first-order sentence semantics uses a language with nullary predicates p_k and one axiom forcing the domain to have exactly one element. The p_k are independent observations; translating p_k to p_(2k) realizes the preceding map. All sentence truth is determined by these predicates in that theory. The filtration by these generators is explicit.

A computable syntactic translation provides a computable upper bound on the required source prefix, by finding indices of translated observations. Computing the least semantic h_f(n) is a separate problem involving equivalence modulo the theory. This release makes no uniform algorithmic claim for that minimum.

## 5. Infinite-dimensional Dirac realization

Christensen and Ivan, *Sums of two-dimensional spectral triples*, Theorem 3.1, establish exact metric recovery for compact metric spaces using countable sums of two-point modules with diagonal mass terms. This is an established construction. It closes the mathematical existence question for the chosen marked metric, while effective construction from arithmetic axioms remains separate.

Here is the explicit version used by this project. Let X be an infinite compact metric space. Select a countable dense set Q of distinct points and enumerate all its unordered unequal pairs (x_j,y_j), j>=0. Write d_j=d(x_j,y_j), m_j=2^j, and take

    H = direct sum over j of C^2,
    pi_j(a) = diag(a(x_j),a(y_j)),
    D_j = [[m_j, 1/d_j], [1/d_j, -m_j]].

Use A=Lip(X) as a dense star-subalgebra of C(X). The representation of C(X) is faithful because evaluations on Q determine a continuous function. Set mu_j^2=m_j^2+d_j^(-2). Define the maximal direct-sum domain

    Dom(D) = {psi in H : sum_j mu_j^2 ||psi_j||^2 < infinity}.

The finite-support vectors lie in Dom(D), so it is dense. Each block is self-adjoint and D_j^2=mu_j^2 I. The adjoint domain is the same square-summability domain, as can be checked against vectors supported in a single block, so D is self-adjoint. Equivalently, diagonalizing each block gives multiplication by the real values ±mu_j on the stated maximal domain.

Let P_N project onto blocks j<N. Squaring and inverting blockwise gives

    ||(1-P_N)(I+D^2)^(-1)|| <= 1/(1+4^N) -> 0.

Finite-rank truncations therefore converge in operator norm, proving compactness. The ordinary resolvent (D-i)^(-1) has tail bound at most (1+4^N)^(-1/2). For every s>0 the trace of (I+D^2)^(-s/2) is bounded by 2 sum_j 2^(-js), hence finite.

A direct block calculation gives

    [D_j,pi_j(a)] = [[0, (a(y_j)-a(x_j))/d_j],
                     [(a(x_j)-a(y_j))/d_j, 0]].

Its norm is |a(y_j)-a(x_j)|/d_j. The mass cancels. Taking the supremum over the dense pairs gives exactly Lip(a): the quotient is continuous off the diagonal, and unequal pairs in Q approximate every unequal pair in X. Bounded commutators preserve Dom(D), first on finite-support vectors and then by closure. Hence this is a spectral triple with

    L_D(a)=||[D,pi(a)]||=Lip(a), and d_D(x,y)=d(x,y).

For the distance equality, every admissible observable is 1-Lipschitz, and the function a(z)=d(z,y) attains the distance between x and y. Finite spaces use the finite direct sum already implemented; the one-point case has a scalar faithful representation and zero distance.

The Lean module checks the block commutator, its energy identity, the block square and symmetry, plus the scalar resolvent bound. The infinite operator domain and compactness argument above are written proofs. They have not been formalized as unbounded operators in Lean.

The mass can be changed without changing L_D. It can also change spectral growth. These realizations recover the marked metric and its observable geometry; their spectra are not claimed to encode an intrinsic dimension or the identity of a theory by themselves.

## 6. Coherent networks and preserved logical consequences

Take the compatible-family space Z of a network of completion spaces. Under the finite-fibre-extension hypothesis already proved in LTR v0.1, each selected projection pi_i:Z->X_i is surjective. If chosen countable markings additionally give pi_i finite delay c_i, the new theorem supplies a geometric and observable bound of 2^(c_i).

Surjectivity preserves truth-locus coverage and emptiness, hence independence. With a fixed sentence-code input, the global cover predicate equals the local entailment predicate. The spectral realization adds operators carrying exactly that marked observable structure. No finite-delay assertion about an arbitrary countably infinite network is automatic: its global marking and each projection's dependence require proof. A countable network gives a metrizable product under the usual countable-language conditions; uncountable networks need a different analytic setting.

For a consistent computably enumerable extension of Q, a sentence phi gives a Lipschitz clopen projection p_phi. Faithfulness yields

    ||pi(1-p_phi)|| = 0 when T entails phi, and 1 otherwise.

Thus a uniform norm-approximation algorithm with absolute error below 1/2, accepting the original sentence names, would decide entailment. The existence of an abstract spectral representation does not supply such an effective procedure. The source of Gödel/Rosser essential undecidability remains an external theorem in this release. No arithmetic diagonalization was added to Lean here.

## 7. Proof and test ledger

| Claim | Evidence in v0.2 |
|---|---|
| Dyadic distance and ultrametric properties | Lean using actual mathlib PiNat distance |
| Delay c iff metric expansion <=2^c | Lean, `translationDelay_iff_distance_bound` |
| Delay c iff bound on all unit-Lipschitz observables | Lean, `translationDelay_iff_observable_bound` |
| Composition, inverse bounds, zero-delay isometry | Lean |
| Mass-shifted block identities and scalar tail estimate | Lean |
| Infinite spectral realization | Written argument using Christensen–Ivan Theorem 3.1 |
| Exact optimal constant from h_f | Written proof; exhaustive finite audits |
| Full first-order interpretation API | Not implemented; supplied interpretation maps must meet stated hypotheses |
| Gödel/Rosser incompleteness | External input, unchanged from v0.1 |
| Novelty | No novelty claim established; the filtration-specific synthesis needs specialist literature review |

There are 27 new Lean theorem declarations, bringing the LTR audit to 59. The first 23 passed at bc26f58b; the full 27 passed at ad0c3db7. The new Python suite has 13 tests. It exhausts all 81 maps from a four-state source to a three-state target and all 648 compatible pairs onward to a two-state target. These test exact depth costs, conservative truth loci, optimal observable witnesses, and finite Dirac algebra. A sharp fixture drops the first two observations: its delay is 2 and both its geometric and observable constants are 4.

## 8. Reproduction and primary references

    lake build Neoplatonic.LTR.Check
    lake env lean Neoplatonic/LTR/Check.lean
    python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v

The spectral repository adds:

    python3 -m unittest discover -s research/logos_topos_spectral -p 'test_*.py' -v
    python3 research/logos_topos_spectral/filtered.py

Primary sources inspected for this extension:

- E. Christensen and C. Ivan, *Sums of two-dimensional spectral triples*, Math. Scand. 100 (2007), 35–60, Theorem 3.1. https://arxiv.org/abs/math/0601024 ; https://doi.org/10.7146/math.scand.a-15015
- J. Pearson and J. Bellissard, *Noncommutative Riemannian Geometry and Diffusion on Ultrametric Cantor Sets*, J. Noncommut. Geom. 3 (2009), 447–480. https://arxiv.org/abs/0802.1336
- Mathlib, PiNat first-disagreement metrics and cylinders: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/PiNat.html

The first source supports the infinite realization. Pearson–Bellissard supplies the alternative tree-based direction, where geometric dimension and measures can be pursued with additional structure. The filtration-delay theorems and exact finite audits in this release are stated independently, with their assumptions visible.
