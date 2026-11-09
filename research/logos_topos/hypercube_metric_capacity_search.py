#!/usr/bin/env python3
"""Exploratory Dirac-metric capacity search for the two-bit truth cube.

Requires NumPy and SciPy. A standard eight-dimensional edge-block control
recovers (1,1,1,1,2,2) exactly. Lower dimensions are formed by merging
selected equal-truth coordinates, then optimizing all real off-diagonal
couplings between distinct truth sectors.

Every pair distance is obtained by numerically minimizing the operator
norm of [D,diag(f)] with f(x)=0, f(y)=1. The optimization has nonsmooth
eigenvalue ties and gives candidate metrics, never an impossibility proof.

Run with --dims 6 7 --seeds 0 1 3 --maxiter 40 for the ordinary
exploratory scan. --all-merges enumerates all equal-truth coordinate
mergings for each dimension. The fixed seed controls the small random
perturbation of each symmetric starting matrix. Every reported distance
is a nested numerical minimum, not a certified value.
"""

from __future__ import annotations

import argparse
from itertools import combinations
from math import sqrt
import numpy as np
from scipy.optimize import minimize

PAIRS = ((0, 1), (0, 2), (1, 3), (2, 3), (0, 3), (1, 2))
HAMMING_TARGET = np.array([1., 1., 1., 1., 2., 2.])
EDGE_LABELS = np.array([0, 1, 0, 2, 1, 3, 2, 3])
MERGE_CHOICES = ((0, 2), (1, 4), (3, 6), (5, 7))


def independent_edge_model() -> tuple[np.ndarray, np.ndarray]:
    D = np.zeros((8, 8), dtype=complex)
    for k in range(0, 8, 2):
        D[k, k + 1] = D[k + 1, k] = 1
    return D, EDGE_LABELS.copy()


def merged_edge_model(merge_set: tuple[int, ...]) -> tuple[np.ndarray, np.ndarray]:
    D8, _ = independent_edge_model()
    keep = list(range(8))
    groups: list[list[int]] = []
    for choice, (a, b) in enumerate(MERGE_CHOICES):
        if choice in merge_set:
            keep.remove(a)
            keep.remove(b)
            groups.append([a, b])
    groups.extend([[k] for k in keep])
    U = np.zeros((8, len(groups)))
    for j, grp in enumerate(groups):
        for k in grp:
            U[k, j] = 1 / sqrt(len(grp))
    labels = EDGE_LABELS[[grp[0] for grp in groups]]
    return U.T @ D8 @ U, labels


def comm_norm(D: np.ndarray, labels: np.ndarray, x: int, y: int,
              free: np.ndarray) -> tuple[float, np.ndarray, np.ndarray, float]:
    f = np.zeros(4)
    f[y] = 1.
    other = [i for i in range(4) if i not in (x, y)]
    f[other] = free
    vals = f[labels]
    K = 1j * D * (vals[np.newaxis, :] - vals[:, np.newaxis])
    w, U = np.linalg.eigh(K)
    z = int(np.argmax(abs(w)))
    return float(abs(w[z])), vals, U[:, z], float(np.sign(w[z]))


def min_norm(D: np.ndarray, labels: np.ndarray, x: int, y: int):
    starts = (np.array([.5, .5]), np.array([0., 1.]))
    results = [
        minimize(lambda z: comm_norm(D, labels, x, y, z)[0], z0,
                 method="Nelder-Mead",
                 options={"maxiter": 180, "xatol": 1e-7, "fatol": 1e-7})
        for z0 in starts
    ]
    winner = min(results, key=lambda r: r.fun)
    return comm_norm(D, labels, x, y, winner.x)


def distances(D: np.ndarray, labels: np.ndarray) -> np.ndarray:
    return np.array([1 / min_norm(D, labels, x, y)[0] for x, y in PAIRS])


class RealDiracSearch:
    def __init__(self, D: np.ndarray, labels: np.ndarray):
        self.labels = labels
        self.n = len(labels)
        self.pairs = np.array([
            (i, j) for i in range(self.n) for j in range(i + 1, self.n)
            if labels[i] != labels[j]
        ], dtype=int)
        self.initial = self.pack(D)

    def pack(self, D: np.ndarray) -> np.ndarray:
        i, j = self.pairs.T
        return D[i, j].real.copy()

    def unpack(self, weights: np.ndarray) -> np.ndarray:
        D = np.zeros((self.n, self.n))
        i, j = self.pairs.T
        D[i, j] = D[j, i] = weights
        return D

    def objective(self, weights: np.ndarray) -> tuple[float, np.ndarray]:
        D = self.unpack(weights)
        vals, gradients = [], []
        i, j = self.pairs.T
        for x, y in PAIRS:
            c, vec, q, sgn = min_norm(D, self.labels, x, y)
            if c < 1e-7:
                return 1e3, np.zeros_like(weights)
            vals.append(c)
            # Envelope-theorem gradient for a simple extremal
            # eigenvalue. At a tie this is one nonsmooth subgradient.
            gradients.append(
                sgn * 2 * np.real(np.conj(q[i])
                                  * (1j * (vec[j] - vec[i])) * q[j])
            )
        vals = np.array(vals)
        gradients = np.stack(gradients)
        mismatch = -np.log(vals) - np.log(HAMMING_TARGET)
        centered = mismatch - mismatch.mean()
        loss = float(np.mean(centered ** 2))
        grad = np.mean(
            2 * centered[:, None] * (-gradients / vals[:, None]), axis=0
        )
        return loss, grad

    def optimize(self, maxiter: int, seed: int = 0):
        rng = np.random.default_rng(seed)
        x0 = self.initial + rng.normal(scale=0.06, size=self.initial.shape)
        result = minimize(self.objective, x0, jac=True,
                          method="L-BFGS-B",
                          options={"maxiter": maxiter, "maxls": 8, "ftol": 1e-7})
        D = self.unpack(result.x)
        d = distances(D, self.labels)
        scale = np.exp(np.mean(np.log(d / HAMMING_TARGET)))
        normalized = d / scale
        error = float(np.sqrt(np.mean(np.log(normalized / HAMMING_TARGET) ** 2)))
        return error, normalized, result


def square_flux(phase: float) -> tuple[np.ndarray, np.ndarray]:
    labels = np.arange(4)
    D = np.zeros((4, 4), dtype=complex)
    for u, v in PAIRS[:4]:
        z = np.exp(1j * phase) if (u, v) == (2, 3) else 1.
        D[u, v], D[v, u] = z, np.conj(z)
    return D, labels


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--maxiter", type=int, default=40)
    parser.add_argument("--all-merges", action="store_true")
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 3])
    parser.add_argument("--dims", nargs="+", type=int, default=[6, 7])
    args = parser.parse_args()
    for n in args.dims:
        if not 4 <= n <= 8:
            parser.error("Only dimensions from 4 through 8 are supported")
    if not args.seeds:
        parser.error("At least one seed is required")

    D8, l8 = independent_edge_model()
    print("Independent H8 control", np.round(distances(D8, l8), 8))
    D4, l4 = square_flux(np.pi)
    print("Four-dimensional pi-flux control", np.round(distances(D4, l4), 8))
    for n in args.dims:
        k = 8 - n
        choices = (list(combinations(range(4), k))
                   if args.all_merges else [tuple(range(k))])
        best = None
        for merge in choices:
            D, labels = merged_edge_model(merge)
            for seed in args.seeds:
                error, d, result = RealDiracSearch(D, labels).optimize(
                    args.maxiter, seed=seed
                )
                if best is None or error < best[0]:
                    best = (error, merge, seed, d, result.nit, result.success)
        assert best is not None
        print(f"H{n}: logRMSE={best[0]:.6f}, merges={best[1]}, "
              f"seed={best[2]}, iters={best[4]}, converged={best[5]}, "
              f"distances={np.round(best[3], 5)}")


if __name__ == "__main__":
    main()
