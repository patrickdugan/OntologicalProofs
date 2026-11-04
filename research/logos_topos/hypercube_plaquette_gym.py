#!/usr/bin/env python3
"""LTR-MAN-09 numerical plaquette gym: four-point Connes distances.

This is a deterministic exploratory check on small Hermitian matrices.
Exact analytic certificates for the 0- and pi-flux cases live in
HYPERCUBE_PLAQUETTE_V09.md. Requires numpy and scipy.

A single 4x4 Dirac matrix need not yield the Hamming square metric,
even though its nonzero entries follow all four Hamming-one edges.
Inserting pi flux through the square changes opposite-vertex distances
from 1 to sqrt(2), while unit-edge distances remain 1.
"""

from __future__ import annotations

import argparse
from math import pi, sqrt
import numpy as np
from scipy.optimize import minimize

EDGES = ((0, 1), (0, 2), (1, 3), (2, 3))
PAIRS = ((0, 1), (0, 2), (1, 3), (2, 3), (0, 3), (1, 2))


def four_cube_dirac(phase: float = 0.0) -> np.ndarray:
    """Return a Hermitian Dirac matrix with phase on the 2--3 edge."""
    D = np.zeros((4, 4), dtype=complex)
    for a, b in EDGES:
        z = np.exp(1j * phase) if (a, b) == (2, 3) else 1.0
        D[a, b], D[b, a] = z, np.conj(z)
    return D


def commutator_norm(D: np.ndarray, f: np.ndarray) -> float:
    """Operator norm ||[D,diag(f)]|| for a real-valued observable f."""
    K = 1j * D * (f[np.newaxis, :] - f[:, np.newaxis])
    eigenvalues = np.linalg.eigvalsh(K)
    return float(np.max(np.abs(eigenvalues)))


def distance(D: np.ndarray, x: int, y: int) -> tuple[float, float, np.ndarray]:
    """Dual metric via min ||[D,f]|| subject to f(x)=0 and f(y)=1.

    The inverse minimum is the Connes distance. The objective is convex
    but nonsmooth; multistart Nelder--Mead is sufficient for this 4x4 gym.
    Analytic certificates are required for claims of exact optimality.
    """
    variables = [k for k in range(D.shape[0]) if k not in (x, y)]
    def unpack(z: np.ndarray) -> np.ndarray:
        f = np.zeros(D.shape[0], dtype=float)
        f[y] = 1.0
        f[variables] = z
        return f
    starts = (
        np.zeros(len(variables)),
        np.ones(len(variables)),
        np.full(len(variables), 0.5),
        np.array([0.37, 0.63], dtype=float),
    )
    best = min(
        (
            minimize(
                lambda z: commutator_norm(D, unpack(z)),
                seed,
                method="Nelder-Mead",
                options={"maxiter": 1800, "xatol": 1e-11, "fatol": 1e-11},
            )
            for seed in starts
        ),
        key=lambda result: result.fun,
    )
    return 1.0 / best.fun, float(best.fun), unpack(best.x)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--phases",
        type=float,
        nargs="*",
        default=[0.0, pi / 2, pi],
        help="Plaquette flux phases, in radians",
    )
    args = parser.parse_args()
    for phase in args.phases:
        D = four_cube_dirac(phase)
        dists = {f"{x}-{y}": distance(D, x, y)[0] for x, y in PAIRS}
        print(
            f"flux={phase / pi:.4f}pi  "
            + "  ".join(f"{pair}:{dist:.9f}" for pair, dist in dists.items())
        )
        if abs(phase) < 1e-10:
            assert abs(dists["0-3"] - 1.0) < 1e-4
            assert abs(dists["0-1"] - 1.0) < 1e-4
        if abs(phase - pi) < 1e-10:
            assert abs(dists["0-3"] - sqrt(2.0)) < 1e-4
            assert abs(dists["1-2"] - sqrt(2.0)) < 1e-4
            assert abs(dists["0-1"] - 1.0) < 1e-4


if __name__ == "__main__":
    main()
