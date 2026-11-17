# MoralRealism: joint ontology, ethics, and agency program

This package commissions the bridges needed to connect an ontology of a first
principle to moral judgment and reliable action. It also supplies a first set of
conditional results and countermodels for review.

## What is delivered

`Kernel.lean` contains 17 theorem declarations. `GroundingBridge.lean` adds five,
including a composition theorem importing the repository's actual
`ConfluentGroundTheory`. `PREMISES.md` identifies what every result consumes.
`COMMISSION.md` specifies the next six work packages and their rejection tests.
The future training and causal-intervention study is specified in
`EXPERIMENT.md`; its execution requires a separate approval.

The initial local run passed 19 Python tests. The exact finite audit enumerated
1,048,576 two-state/two-action systems, including all four execution predicates,
all initial sets, every transition relation, and all gates and laws. Of 21,584
systems satisfying the execution contract, zero had a forbidden reachable
effect. There were 4,559 satisfying systems with an executable reachable effect.
Each of the four execution premises has a deletion counterexample with the other
three retained. The domain and counts are recorded in `finite_audit.json`.
These are enumerated logical cases; they supply no statistical evidence about LLMs.

## Verification

The authoring environment has no Lean/Lake binary, and outbound GitHub cloning
failed at DNS resolution. The local receipt therefore reports
`PYTHON_PASS_LEAN_NOT_RUN`. Every Lean declaration remains a draft until a
successful kernel run is available for its exact source revision.

From the repository root:

```sh
python3 MoralRealism/verify.py --python-only
# With the root-pinned Lean/mathlib toolchain installed and dependencies available:
lake exe cache get
python3 MoralRealism/verify.py --output /tmp/moral-realism-verification.json
```

The default verifier requires successful compilation and matches the complete
22-theorem inventory against `#print axioms`. The permitted kernel dependencies
are `propext`, `Classical.choice`, and `Quot.sound`. Its lexical source scan is an
additional smoke test. A path-scoped PR workflow runs both checks using pinned
Action revisions and the existing root Lean 4.35.0 toolchain.

## The composition target

`joint_source_execution` constructs a first principle with the supplied value
property and establishes the supplied ground-indexed law for every reachable
execution edge. Its behavioral premise is an `ExecutionContract` for that law:
initial validity, invariant preservation, complete mediation, and gate soundness.

The invariant covers arbitrary finite prefixes. Self-modification belongs in the
state and transition relation. Safety of a proposed update requires the same
preservation obligation as every other effect.

`ConcealedViolation` records a lawful reported action paired with a forbidden
executed action. `OversightViolationGap` records lawful behavior under observation
and a violation without observation. Private motives and latent preferences have
no representation in these definitions. `CLAIMS.md` specifies the supported claims.

## Preserved work and source pins

Base: `ab6ef3de7a8b17bf44dccda892f484845d8776a8`.

The existing `Neoplatonic/` modules and root build files remain unchanged. The
Divine Elegance import is PR #1 at
`d81b9bed02b4e13483dda07abf94f4ac79c07324`; its 4.22.0 project remains separate.
PR #2 at `24e7c592394b25614c7bdbde9841933c93bfdcba` retains the arithmetic and
spectral work. This package imports neither open PR.

The existing Divine Elegance information-bottleneck proof is acknowledged in
`PREMISES.md`; the small standalone collision lemma here keeps this package
buildable from main. The six work orders reserve separate paths. Nothing in this
change executes training, downloads a checkpoint, changes an account, or merges work.
