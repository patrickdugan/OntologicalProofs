#!/usr/bin/env python3
"""Complex-Hermitian metric capacity search for the two-bit Boolean cube.

Imports the real-valued-observable dual solver from
hypercube_metric_capacity_search.py and generalizes its Dirac matrices
to complex Hermitian cross-profile couplings.

The inner norm minimization is convex but nonsmooth; the outer search is
nonconvex and uses a single spectral subgradient at ties. Reported
distances are exploratory numerical results. An exact realization
requires a separate analytic or formally verified certificate.

Run, for example:
 python research/logos_topos/hypercube_complex_metric_search.py \
     --dims 6 7 --seeds 0 1 2 --maxiter 60
"""

from __future__ import annotations

import argparse
from itertools import combinations
from math import sqrt

import numpy as np
from scipy.optimize import minimize

from hypercube_metric_capacity_search import (
    EDGE_LABELS, HAMMING_TARGET, PAIRS, RealDiracSearch,
    independent_edge_model, merged_edge_model, min_norm,
)


class ComplexDiracSearch(RealDiracSearch):
    """Optimize real and imaginary off-diagonal Dirac entries separately."""

    def pack(self, D: np.ndarray) -> np.ndarray:
        i, j = self.pairs.T
        return np.r_[D[i, j].real, D[i, j].imag]

    def unpack(self, weights: np.ndarray) -> np.ndarray:
        D = np.zeros((self.n, self.n), dtype=complex)
        i, j = self.pairs.T
        q = len(i)
        z = weights[:q] + 1j * weights[q:]
        D[i, j] = z
        D[j, i] = np.conj(z)
        return D

    def objective(self, weights: np.ndarray) -> tuple[float, np.ndarray]:
        D = self.unpack(weights)
        values, gradients = [], []
        i, j = self.pairs.T
        for x, y in PAIRS:
            c, vals, eigvec, sign = min_norm(D, self.labels, x, y)
            if c < 1e-8:
                return 1000.0, np.zeros_like(weights)
            values.append(c)
            diff = vals[j] - vals[i]
            overlap = np.conj(eigvec[i]) * eigvec[j]
            grad_real = sign * 2 * np.real(1j * diff * overlap)
            grad_imag = sign * (-2) * diff * np.real(overlap)
            gradients.append(np.r_[grad_real, grad_imag])
        values = np.asarray(values)
        grad = np.stack(gradients)
        mismatch = -np.log(values) - np.log(HAMMING_TARGET)
        mismatch -= mismatch.mean()
        return (
            float(np.mean(mismatch ** 2)),
            np.mean(2 * mismatch[:, None] * (-grad / values[:, None]), axis=0),
        )

    def optimize(self, maxiter: int, seed: int = 0):
        rng = np.random.default_rng(seed)
        weights = self.initial + rng.normal(scale=0.09, size=self.initial.shape)
        res = minimize(
            self.objective, weights, jac=True, method="L-BFGS-B",
            options={"maxiter": maxiter, "maxls": 8, "ftol": 1e-8},
        )
        D = self.unpack(res.x)
        values = np.array([1 / min_norm(D, self.labels, x, y)[0] for x, y in PAIRS])
        # Rescale away the arbitrary global Dirac coupling magnitude.
        scale = np.exp(np.mean(np.log(values / HAMMING_TARGET)))
        d = values / scale
        err = float(np.sqrt(np.mean(np.log(d / HAMMING_TARGET) ** 2)))
        return err, d, res


def multiplicity_model(multiplicity: tuple[int, ...]) -> tuple[np.ndarray, np.ndarray]:
    """A faithful diagonal representation with arbitrary positive multiplicities."""
    if len(multiplicity) != 4 or min(multiplicity) < 1:
        raise ValueError("Supply four positive vertex multiplicities")
    labels = np.repeat(np.arange(4), multiplicity)
    D = np.zeros((len(labels), len(labels)), dtype=complex)
    hypercube_edges = {(0, 1), (0, 2), (1, 3), (2, 3)}
    for i, j in combinations(range(len(labels)), 2):
        a, b = int(labels[i]), int(labels[j])
        if (a, b) in hypercube_edges:
            D[i, j] = D[j, i] = 1 / sqrt(multiplicity[a] * multiplicity[b])
    return D, labels


def models_for_dimension(n: int, all_merges: bool, partitions: bool):
    if partitions:
        pattern_map = {
            6: ((3, 1, 1, 1), (2, 2, 1, 1), (2, 1, 1, 2)),
            7: ((4, 1, 1, 1), (3, 2, 1, 1), (3, 1, 1, 2), (2, 2, 2, 1)),
        }
        for mult in pattern_map.get(n, ()):
            yield f"mult={mult}", multiplicity_model(mult)
    k = 8 - n
    merges = combinations(range(4), k) if all_merges else (tuple(range(k)),)
    for merge in merges:
        yield f"merge={merge}", merged_edge_model(tuple(merge))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--maxiter", type=int, default=40)
    parser.add_argument("--seeds", nargs="+", type=int, default=[0, 1, 2])
    parser.add_argument("--dims", nargs="+", type=int, default=[6, 7])
    parser.add_argument("--all-merges", action="store_true")
    parser.add_argument("--partitions", action="store_true")
    args = parser.parse_args()
    for n in args.dims:
        if n not in (6, 7):
            parser.error("Complex scan is currently scoped to dimensions 6 and 7")
        best = None
        for name, (D, labels) in models_for_dimension(
            n, args.all_merges, args.partitions
        ):
            for seed in args.seeds:
                loss, d, opt = ComplexDiracSearch(D, labels).optimize(
                    args.maxiter, seed=seed
                )
                if best is None or loss < best[0]:
                    best = (loss, name, seed, d, opt.nit, opt.success)
        assert best is not None
        print(
            f"H{n}: logRMSE={best[0]:.6f}, {best[1]}, "
            f"seed={best[2]}, iters={best[4]}, converged={best[5]}, "
            f"distances={np.round(best[3], 6)}",
            flush=True,
        )


if __name__ == "__main__":
    main()
