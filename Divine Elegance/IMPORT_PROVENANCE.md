# Divine Elegance import provenance and status

This directory is an artifact-only import of the author's **Divine Elegance: Muʿtaziliya After Gödel** formal research package v0.1, associated with manuscript v2.3.

## Source and preservation

- Source archive: `divine_elegance_formal_pack_v01.zip` (Library version 2), 216,569 bytes.
- Archive SHA-256: `8d4578cae13757f95249e3d39601349d7c83cc3e08848ed909354cfdcce906a6`.
- All 60 original archive files are preserved byte-for-byte beneath `Divine Elegance/`.
- The original `manifest_sha256.json` verifies its 59 listed files; the manifest does not list itself. This import note is an additional repository document, not an original archive file.
- The Lean-only archive is an identical 11-file subset of this full pack; it is not imported a second time.
- The repository's existing Neoplatonic project and root Lean 4.35.0 configuration are unchanged.

## Evidence status

- **38 drafted Lean theorem/lemma declarations:** 18 new declarations and 20 carried-over declarations in `QuranModal.lean`.
- **Lean kernel compilation: NOT_RUN.** These drafts must not be described as machine-checked proofs.
- The package records six completed synthetic Python jobs and **7 passing unit tests in the authoring environment**. This import did not rerun them.
- The **96-case ikhtilāf registry** is staged research metadata, not a globally solved or reconciled proposition set.
- **DE-01 through DE-09** are nine queued work orders, not jobs launched by this import.
- Theological interpretations remain source-dependent premises; synthetic fixtures do not establish claims about actual people, divine judgment, or historical events.

## Isolation and execution

The nested project retains `leanprover/lean4:v4.22.0` and its own `lakefile.toml`. Its workflow remains at `Divine Elegance/.github/workflows/lean_and_python.yml`, not the repository-root workflow directory, and is inactive. Do not move it to the root without a separately reviewed execution plan.

No package code, compilation, experiments, tests, or workflows were executed as part of publication. No merge or deployment is included.

Start with [the original package README](README.md), [the proof ledger](PROOF_LEDGER.md), and [the original verification record](VERIFICATION.md).
