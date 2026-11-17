# Divine Elegance agentic research queue

## Stage rules

- **Codex is the local build/orchestration worker.** Other model reviewers receive text/files and return review notes; they should not independently modify the authoritative manuscript.
- Freeze this bundle and the v2.3 manuscript baseline by SHA-256 before any edits. Every job returns changes as a distinct patch or PR and a machine-readable receipt.
- Agent output is **candidate evidence**. Approval of a theological premise requires Arabic/source scrutiny; empirical results require independent data and preregistration; only a Lean kernel can certify Lean proofs.
- Separate historical/factual evidence, hypothetical mathematical analogies, and normative claims. The book has legitimate literary freedom while its proof ledger must expose each boundary.
- Default offline. No spending, live deployments, brute-force search, autonomous attack, secret retrieval, training on identifiable religious/private attributes, or changes to real infrastructure without a separately authorized plan.

## Recommended order

| Priority | Job | Worker and hardware | Entry condition | Deliverable |
| --- | --- | --- | --- | --- |
| P0 | DE-01 Kernel-check core Lean | Codex, local CPU | Bundle checked out | Lean build log, axiom inventory, minimal fixes |
| P0 | DE-02 96-case joint ikhtilāf pilot | Codex + Arabic-source reviewer, CPU | Registry staged, 12 cases selected | Typed claim ledger, local/global SAT receipts, unsat core if any |
| P0 | DE-03 Mercy-justice decision sufficiency | Codex, local CPU | Rights features and relevant transforms preregistered | Cross-model counterexamples, matched baselines and counterfactuals |
| P1 | DE-04 Sign/Source/Authority esoteric audit | Arabic reader + red team | Frozen verse and hadith editions | Independent annotation, theological premise map |
| P1 | DE-05 RSI authorized-effects harness | Codex + external review, CPU; GPU only for preapproved matched models | Reuse Control-Harness typed-v2 | Held-out controller-comparison vector, provenance DAG, costs |
| P1 | DE-06 Code-19 negative controls | Codex + philology reviewer, CPU | Exact Arabic rasm + feature-selection protocol pinned | Multiplicity-corrected exploratory analysis |
| P1 | DE-07 Conformal and restitution robustness | Codex, CPU | Numerical grid and marker scope fixed | Refinement-convergent geodesics, sensitivity and failure cases |
| P2 | DE-08 6GW defensive fiqh source audit | Qualified legal/fiqh reviewers | Limited to lawful offline examples | Axioms-to-rulings matrix, open disagreements and HOLDs |
| P2 | DE-09 Interchapter concept-lattice replication | Independent mathematician + annotators, CPU | Blind annotation rubric agreed | Interrater agreement, lattice comparison, overlap-vs-chance |

### Dependencies

- DE-01 first because kernel checking prevents false proof claims.
- DE-02 can begin in parallel with DE-01 because the 96-entry registry is now staged, but source fields remain **unformalized**.
- DE-03 uses the proof shell in DE-01; its empirical extension requires independent annotation of which features are morally relevant.
- DE-05 reuses [Control-Harness](https://github.com/MoralityLabAI/Control-Harness) rather than forking a duplicate experiment into the book.
- DE-06/07/09 are independent CPU research and can run as low-cost bounded workers.
- DE-08 needs substantive jurisprudential review before any classification is treated as advice.

### Required receipt (every job)

```json
{
  "job_id": "DE-xx",
  "baseline_sha256": "...",
  "source_revisions": [],
  "commands": [],
  "artifacts": [{"path": "...", "sha256": "..."}],
  "tests": {"passed": [], "failed": [], "not_run": []},
  "evidence_class": "kernel_checked | source_reviewed | offline_synthetic | model_pilot | unverified",
  "falsifiers_checked": [],
  "limitations": [],
  "next_blocker": null
}
```

Results are promoted to manuscript facts only after their own evidentiary standards have been met. A verified conditional theorem remains conditional, even if its proof and formatting are flawless.
