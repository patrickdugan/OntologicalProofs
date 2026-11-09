#!/usr/bin/env python3
"""Re-evaluate archived 6D and 7D Dirac candidates independently.

Reconstruct Hermitian matrices from the upper triangle of the frozen
JSON artifact and recompute all six dual Connes distances. The inner
dual solve uses scipy.optimize on real observables, which suffices for
Hermitian Dirac matrices. Approximate checks are numerical and are not
Lean proofs or feasibility certificates.

Run:
  python research/logos_topos/verify_hypercube_candidates.py
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np

from hypercube_metric_capacity_search import (
    HAMMING_TARGET, PAIRS, distances, independent_edge_model,
)


def reconstruct(candidate: dict) -> tuple[np.ndarray, np.ndarray]:
    n = candidate["dim"]
    labels = np.asarray(candidate["labels"], dtype=int)
    assert labels.shape == (n,) and set(labels) == {0, 1, 2, 3}
    D = np.zeros((n, n), dtype=complex)
    for i, j, real, imag in candidate["upper_triangle"]:
        assert 0 <= i < j < n and labels[i] != labels[j]
        assert D[i, j] == 0
        D[i, j] = complex(real, imag)
        D[j, i] = complex(real, -imag)
    np.testing.assert_allclose(D, D.conj().T, atol=1e-13, rtol=0)
    return D, labels


def main() -> None:
    D8, labels8 = independent_edge_model()
    np.testing.assert_allclose(
        distances(D8, labels8), HAMMING_TARGET, atol=1e-5, rtol=0
    )
    print("H8 control: exact Hamming distances within numerical tolerance")
    source = Path(__file__).with_name("hypercube_6d_7d_candidates.json")
    record = json.loads(source.read_text(encoding="utf-8"))
    assert record["schema"] == "LTR-MAN-11-01"
    for candidate in record["candidates"]:
        assert tuple(map(tuple, candidate["distance_order"])) == PAIRS
        D, labels = reconstruct(candidate)
        d = distances(D, labels)
        archived = np.asarray(candidate["scaled_distances"])
        largest_error = float(np.max(np.abs(d - archived)))
        assert largest_error < 2e-3, (candidate["dim"], largest_error)
        log_error = float(np.sqrt(np.mean(np.log(d / HAMMING_TARGET) ** 2)))
        assert abs(log_error - candidate["log_rmse"]) < 2e-3
        print(
            f"H{candidate['dim']} complex={candidate['complex_couplings']} "
            f"logRMSE={log_error:.7f} max_drift={largest_error:.3g} "
            f"distances={np.round(d, 6)}"
        )


if __name__ == "__main__":
    main()
