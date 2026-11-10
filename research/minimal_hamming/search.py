#!/usr/bin/env python3
"""Numerical reconnaissance for the smallest 2-bit Hamming spectral triple.

The Lean theorems in LTR-MAN-53/54 give the rigorous 5D obstruction and
8-coordinate construction. This script tests candidate 6D/7D matrices.
Every numerical result here is exploratory, not a mathematical proof.

Install: python -m pip install numpy scipy
Smoke:   python research/minimal_hamming/search.py --smoke
Search:  python research/minimal_hamming/search.py --dimension 6 --seeds 3
"""
from __future__ import annotations

import argparse
import json
import time
from typing import Sequence

import numpy as np
from scipy.optimize import least_squares, minimize

PAIRS = ((0, 1), (0, 2), (1, 3), (2, 3), (0, 3), (1, 2))
TARGET = np.asarray((1.0, 1.0, 1.0, 1.0, 2.0, 2.0))

# Boolean-square symmetry representatives of every positive multiplicity
# partition for dimensions 6 and 7.
PATTERNS: dict[int, dict[str, tuple[int, ...]]] = {
    6: {
        "three_one": (0, 0, 0, 1, 2, 3),
        "two_two_adjacent": (0, 0, 1, 1, 2, 3),
        "two_two_opposite": (0, 0, 3, 3, 1, 2),
    },
    7: {
        "four_one": (0, 0, 0, 0, 1, 2, 3),
        "three_two_adjacent": (0, 0, 0, 1, 1, 2, 3),
        "three_two_opposite": (0, 0, 0, 3, 3, 1, 2),
        "two_two_two": (0, 0, 1, 1, 2, 2, 3),
    },
}


def matrix_from_couplings(
    couplings: np.ndarray, label: Sequence[int], pairs: np.ndarray
) -> np.ndarray:
    """Build a real symmetric Dirac matrix, omitting commuting fibre blocks."""
    d = np.zeros((len(label), len(label)))
    d[pairs[:, 0], pairs[:, 1]] = couplings
    return d + d.T


def cross_fibre_pairs(label: Sequence[int]) -> np.ndarray:
    return np.asarray(
        [(i, j) for i in range(len(label)) for j in range(i + 1, len(label))
         if label[i] != label[j]],
        dtype=int,
    )


def connes_distances(
    d: np.ndarray,
    label: Sequence[int],
    *,
    ftol: float = 1e-7,
    maxiter: int = 100,
) -> tuple[np.ndarray, bool]:
    """Compute six real-observable Connes distances using spectral constraints.

    For Hermitian D, phase-rotation and taking a real part show that
    complex observables give the same pairwise supremum as real ones.
    Fix the additive gauge f(0) = 0. The matrix i[D,pi(f)] is Hermitian.

    The inner optimization maximizes a linear functional over the convex
    feasible region -I <= i[D,pi(f)] <= I. SLSQP uses a spectral-radius
    inequality with a numerical tolerance. Inner failures are reported.
    """
    lab = np.asarray(label, dtype=int)
    assert d.shape == (len(lab), len(lab))
    assert np.allclose(d, d.T.conj())
    assert sorted(set(label)) == [0, 1, 2, 3]

    def spectral_radius(z: np.ndarray) -> float:
        values = np.r_[0.0, z][lab]
        comm = 1j * (d * (values[None, :] - values[:, None]))
        eigenvalues = np.linalg.eigvalsh(comm)
        return float(np.max(np.abs(eigenvalues)))

    result = []
    all_success = True
    for u, v in PAIRS:
        c = np.zeros(3)
        if u:
            c[u - 1] += 1.0
        if v:
            c[v - 1] -= 1.0

        opt = minimize(
            lambda z: -float(c @ z),
            np.zeros(3),
            method="SLSQP",
            constraints=({"type": "ineq", "fun": lambda z: 1.0 - spectral_radius(z)},),
            options={"maxiter": maxiter, "ftol": ftol, "disp": False},
        )
        feasible = spectral_radius(opt.x) <= 1.0 + 1e-6
        all_success = all_success and bool(opt.success and feasible)
        result.append(float(c @ opt.x) if feasible else float("nan"))
    return np.asarray(result), all_success


def hamming_8d_control() -> tuple[np.ndarray, list[int]]:
    """Four independent 2x2 edge blocks, the MAN-54 upper-bound model."""
    label = [0, 1, 0, 2, 1, 3, 2, 3]
    d = np.zeros((8, 8))
    for i in range(0, 8, 2):
        d[i, i + 1] = d[i + 1, i] = 1.0
    return d, label


def fit_pattern(
    label: Sequence[int], *, seed: int, max_nfev: int, inner_maxiter: int
) -> dict:
    edge_indices = cross_fibre_pairs(label)
    rng = np.random.default_rng(seed)
    calls = 0

    def residual(theta: np.ndarray) -> np.ndarray:
        nonlocal calls
        calls += 1
        d = matrix_from_couplings(theta, label, edge_indices)
        distances, converged = connes_distances(d, label, maxiter=inner_maxiter)
        if not converged or not np.all(np.isfinite(distances)) or min(distances) <= 0:
            return np.ones(len(TARGET)) * 100.0
        # If D is scaled by s, each Connes distance scales by 1/s.
        # Fit a common distance scale before comparing pairwise geometry.
        scale = float((TARGET @ distances) / (distances @ distances))
        return scale * distances - TARGET

    start = time.monotonic()
    fit = least_squares(
        residual,
        rng.normal(0, 0.6, len(edge_indices)),
        max_nfev=max_nfev,
        ftol=1e-6,
        xtol=1e-6,
        gtol=1e-6,
    )
    matrix = matrix_from_couplings(fit.x, label, edge_indices)
    distances, inner_ok = connes_distances(matrix, label, maxiter=inner_maxiter)
    scale = float((TARGET @ distances) / (distances @ distances))
    err = scale * distances - TARGET
    return {
        "dimension": len(label),
        "label": list(label),
        "seed": seed,
        "outer_evaluations": int(fit.nfev),
        "inner_solver_all_converged": bool(inner_ok),
        "residual_evaluation_count": calls,
        "scaled_distances": (scale * distances).tolist(),
        "target_distances": TARGET.tolist(),
        "scale_invariant_l2_error": float(np.linalg.norm(err)),
        "scale_invariant_linf_error": float(np.max(np.abs(err))),
        "seconds": round(time.monotonic() - start, 3),
        "dirac_matrix": matrix.tolist(),
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dimension", type=int, choices=(6, 7), default=6)
    ap.add_argument("--seeds", type=int, default=1)
    ap.add_argument("--max-nfev", type=int, default=15)
    ap.add_argument("--inner-maxiter", type=int, default=100)
    ap.add_argument("--smoke", action="store_true")
    args = ap.parse_args()

    if args.smoke:
        d, label = hamming_8d_control()
        distances, ok = connes_distances(d, label)
        report = {
            "control": "four independent edge blocks; eight coordinates",
            "inner_solver_all_converged": ok,
            "distances": distances.tolist(),
            "target": TARGET.tolist(),
            "max_absolute_error": float(np.max(np.abs(distances - TARGET))),
        }
        print(json.dumps(report, indent=2))
        if not ok or report["max_absolute_error"] > 1e-4:
            raise SystemExit("Numerical 8D control failed")
        return

    records = []
    for pattern, label in PATTERNS[args.dimension].items():
        for seed in range(args.seeds):
            row = fit_pattern(
                label, seed=seed, max_nfev=args.max_nfev,
                inner_maxiter=args.inner_maxiter
            )
            row["pattern"] = pattern
            records.append(row)
            print(json.dumps(row, sort_keys=True), flush=True)
    print(json.dumps({
        "experimental_scope": "real symmetric D only; numerical heuristic",
        "best_by_pattern": {
            name: min(
                (r["scale_invariant_l2_error"] for r in records if r["pattern"] == name),
                default=None,
            ) for name in PATTERNS[args.dimension]
        },
    }, sort_keys=True))


if __name__ == "__main__":
    main()
