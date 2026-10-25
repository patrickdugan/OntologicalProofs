# Divine Elegance: Muʿtaziliya After Gödel
## Formalization and agentic empirical research pack v0.1

This package derives from the *Axiomatic Overture* in manuscript v2.3 (commit-independent local source). It preserves the earlier Ibn ʿArabī × Mullā Ṣadrā `QuranModal.lean` research archive, carries E0–E8 into conditional Lean formulations, and provides **synthetic** experimental scaffolds and separately dispatchable worker contracts.

### Run the checks now (Python 3.10+)

```bash
python3 run_all.py
python3 scripts/check_placeholders.py
```

No packages outside the Python standard library are needed. Data and recorded outcomes land in `artifacts/`. All available local synthetic fixtures passed in the authoring environment.

### Run the Lean kernel (trusted workstation / CI)

```bash
# Installer and toolchain must be obtained through your approved software channel.
cat lean-toolchain
lake build
lake env lean QuranModal.lean
lake env lean DivineElegance.lean
python3 scripts/check_placeholders.py
```

CI recipe: `.github/workflows/lean_and_python.yml`. This file assumes the project is the repository root; place it under a dedicated repository or adapt paths before copying into a larger repo. The installer command in CI currently fetches the elan installer from upstream, so a hardened runner should vendor or pin its digest.

### Source map

- `source/Axiomatic_Overture.md`: **exact manuscript text** from v2.3.
- `source/Elegance_Keys_19_Chapters.md`: author's per-chapter E0–E8 mapping.
- `QuranModal.lean`: original v0.8, included verbatim and **not edited**.
- `DivineElegance/*.lean`: new conditional lemmas, counterexamples, and policy model.
- `PROOF_LEDGER.md`: distinction between proven consequences, drafted Lean, and unresolved source premises.
- `experiments/e01...e06...`: synthetic scenario generators; **not evidence about actual people, divine judgment, AI safety or historical miracles**.
- `jobs/`: isolated prompts for Codex, computational workers and scholarly reviewers.
- `AGENTIC_ROADMAP.md`: priority, dependencies, evaluation methods, and safe job boundaries.
- `artifacts/RUN_STATUS.json`: audit trail from local execution; no Lean check has run.

### Restrictions for downstream agents

Treat Qur'anic and hadith interpretations as source-dependent propositions. Quote Arabic precisely and preserve verse context. Never convert a formal analogy into a verified divine claim, a numeric toy model into a judgment of souls, or a provisional 6GW fiqh exercise into permission for intrusion or violence. Avoid editing the manuscript until results have been independently reviewed. Use synthetic datasets for AI tests, and separate permissions for any live system work.
