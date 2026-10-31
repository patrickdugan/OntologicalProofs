# Storyworld verification receipt

Implementation commit: `6c3d11f706bbb3a816a3db6775fca54319668e01`.

[GitHub Actions run 41184977544](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41184977544) completed successfully on 2026-10-31. Job `124489968459` logs were inspected after completion.

**62 tests passed, zero skips and zero failures.** This includes `test_gymnasium_checker`, which had been skipped in the network-isolated authoring environment. The historical local receipt under `storyworld/receipts/cpu.json` retains its original local status; this CI receipt supplies the subsequent check.

CI used Python 3.11.17, Gymnasium 1.2.2 and PyTorch 2.5.1+cpu. The workflow rebuilt the native world, ran the upstream SweepWeave validator and reproduced 5,000 random-policy campaigns. Ending counts were 1,000 / 1,085 / 1,031 / 937 / 947. The world semantic hash was `213d262ada0b1722101436ff876bb6ae873f40bb2ce38f9285a2509a4a53e739`.

The scripted gym policies reproduced the expected controls, including uniform violation with zero oversight gap, accurate disclosure of a violation, and unknown outcomes for missing reports. The Torch test performed backpropagation on random toy weights.

HF/PEFT pretrained-model execution, CUDA execution and native SweepWeave browser/UI parity remain unrun. The four-A100 launcher is implemented and awaits an approved local checkpoint and provider budget. No model-alignment result is claimed.

Entry points: [implemented handoff](handoff.md), [scientific review and cluster brief](storyworld/SILICO_REVIEW.md), [run instructions](storyworld/README.md).
