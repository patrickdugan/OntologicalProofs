# DE-02 · Global Qur'anic interpretation, real 96-case registry

**Owner:** Codex source/solver coordinator with an independent Arabic reviewer. **Priority:** P0. **Hardware:** local CPU. **Scope:** 12-case pilot first, then 96 if evidence is ready.

## Verified inputs and limits

`source/ikhtilaf_96_registry.json` has 96 IDs, names, provisional route labels and two source URLs per row. `source/ikhtilaf_96_staging.csv` has empty semantic/provenance columns. Existing v0.8 `QuranModal.lean` and Python model checker provide a small independently auditable regression fixture. **The registry alone does not encode 96 constraints**, so do not run a solver on the provisional route labels as though they were propositions.

## Work

1. Freeze Arabic rasm version and verse scope. Select a pilot of 12 cases, including IK-036, IK-059, IK-073 and nine drawn across distinct domains/routes; publish the selected IDs before textual interpretation.
2. For each case, record speaker, audience, referent, event/time, modal scope, predicate sense and language-supporting evidence, including at least one adversarial alternative reading. Mark unverified fields `UNKNOWN`.
3. Translate separately warranted claims into typed logical propositions. Use explicit selectors for mutually exclusive readings; retain source and confidence metadata separately from truth constraints.
4. Build SAT/SMT with provenance mappings (Z3 allowed after explicit installation). Check individual, paired and **global** satisfiability. When UNSAT, extract a minimal unsatisfiable core and independently reread its Arabic commitments.
5. Use the original 32-assignment truth table as a regression; 10/9/6/5 counts must match. Compare blind reviewer interpretations, then rerun after disagreements are adjudicated.

## Falsifier and stop

One consistent choice for each case may fail globally. The worker must return the smallest conflicting subset rather than hand-wave new meanings into the text. An apparent conflict dissolving after genuine speaker/time disambiguation is a success only if that disambiguation is independently textually justified. Stop short of claiming all 96 reconcile until all 96 share one validated model.

## Deliver

`typed_claims.json`, `source_ledger.csv`, `pilot_sat_results.json`, `unsat_cores.json`, `evidence_gaps.md`, `global_model_witness.json` (if one exists), reviewer disagreements, and command receipts. Do not edit the manuscript automatically.
