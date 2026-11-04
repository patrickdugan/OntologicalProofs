# LTR-UG-01: finite Unique Games / marked Stone / spectral frustration bridge

**Date:** 2026-11-04. **Status:** elementary identities, with a Lean
gauge-defect module and exhaustive standalone Python tests; the reduction
from 3SAT is cited from OpenAI's September 2026 manuscript, not reproved.

## Defined objects

For a finite oriented multigraph with nonempty edge-occurrence set `E`,
let `K` be a finite abelian translation group and let `c:E→K`.
The finite discrete Stone space of labelings is `X=K^V`. The clopen
edge satisfaction set and its characteristic projection are

    C_e = {a∈X | a(target(e)) - a(source(e)) = c(e)}
    P_e = 1[C_e] ∈ C(X).

The positive element `A = |E|⁻¹ Σ_e P_e` acts as multiplication by
the fraction of edges satisfied by a labeling. In a faithful multiplication
representation, `||A|| = max_(a∈X) A(a) = val(G)`.
Then `H = 1-A` is positive and its minimum spectral value equals
`1-val(G)`. The full diagonal matrix is exponential in `|V|`;
the *description* as a sum of local clopen projectors is polynomial.

**Zero-edge convention:** `val(G)=1`, `A=1`, `H=0`.

## Gauge invariance and correction

Write `da(e)=a(target(e))-a(source(e))` and `D_c(a)=c-da`.
Under `c↦c+dp`, `a↦a+p`, the defect `D_c(a)` is invariant.
Lean's `UniqueGamesFinite.lean` proves equality of defects and bad-edge
sets for any additive commutative group.

Choose a spanning forest and attach one 2-cell along each fundamental
cycle. This *specified* cell attachment kills first cohomology:
`ker(d₁)=im(d₀)`. If `F_c=d₁c`, then

    min_a |supp(c-da)| = min_(ξ:d₁ξ=F_c) |supp ξ|.

Proof: each vertex labeling provides `ξ=c-da`. Conversely, a correction
with matching curvature has `d₁(c-ξ)=0`, so the vanishing first
cohomology gives `c-ξ=da`. The support counts whole edges, rather
than individual bit coordinates.

The identification depends on the attached 2-cells. A bare graph has
no 2-cochain curvature, while graph cycle holonomy remains defined.

## Complexity consequence (conditional)

The OpenAI theorem states a polynomial-time reduction from 3SAT to
explicit translation Unique Games with fixed completeness at least
`1-ε` and soundness at most `δ`, for fixed `0<ε,δ<1/2`.
Assuming the reduction is sound, an efficiently constructible
polynomial-dimensional rational Hermitian matrix `M_G`, with
polynomial-bit entries and `| ||M_G||-val(G) | ≤ τ` for fixed
`2τ < 1-ε-δ`, would yield a polynomial-time 3SAT decision algorithm:
rational Hermitian matrix norms can be approximated in polynomial time.
Consequently, unless P=NP, no **uniform** representation satisfying
all these efficiency and approximation requirements exists.

There is no obstruction to exponential-dimensional faithful
representations, or to a small representation whose entries already
encode an NP-hard optimization.

## Reproduce

    lake build Neoplatonic.LTR.Check
    lake env lean Neoplatonic/LTR/Check.lean
    python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v

The Lean audit scope covers algebraic gauge invariance. The norm identity
is a written consequence of finite C(X); curvature correction and
conditional spectral-compression complexity remain written proofs.
Independent proof review of the upstream UGC claim remains relevant.

Sources:
- https://github.com/openai/math/blob/main/lean/OAI/Computability/UniqueGames/Theorem.lean
- https://github.com/MoralityLabAI/EvalMath/blob/main/paper/unique_games_topology_eth.md
- https://github.com/patrickdugan/OntologicalProofs/blob/main/research/logos_topos/README.md
