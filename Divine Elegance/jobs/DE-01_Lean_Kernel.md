# DE-01 · Prove the actual proof project

**Owner:** Codex, isolated local checkout. **Hardware:** CPU. **Authority:** edits only within this formal proof package; no manuscript mutation. **Priority:** P0.

## Frozen source

`lean-toolchain = leanprover/lean4:v4.22.0`, original `QuranModal.lean` v0.8 plus new `DivineElegance/*.lean`. Reproduce `source/quran_modal_v08_verification.json` while keeping the source unchanged.

## Execute

```bash
lake build
lake env lean QuranModal.lean
lake env lean DivineElegance.lean
python3 scripts/check_placeholders.py
python3 run_all.py
```

Resolve compilation errors minimally and do not introduce `sorry`, `admit`, `unsafe`, `axiom`, or a supplementary unverified premise to make a theorem pass. Record the exact Lean version and SHA-256 of every file. Add an `#print axioms <qualified-theorem>` audit report for every new theorem and explain standard Lean metatheoretic axioms separately from invented domain axioms. On failure, preserve diagnostics with file and line numbers and return the smallest source patch.

## Acceptance

Lean kernel accepts every new theorem and all baseline v0.8 theorems. Full `lake build`, explicit imports, placeholder scan, and seven Python tests pass on the checked source. Produce `lean_kernel_receipt.json` with the commands, toolchain hash, source commits, theorem declaration list and remaining assumptions. **Until this passes, label all Lean files drafted/unverified.**
