#!/usr/bin/env python3
"""MAN-98 finite diagnostic for 2+2 saturated signed-witness canonical forms.

Run: python research/logos_topos/man98_signed_witness_scan.py
Requires numpy. This numerical check is not a proof of the labelled
Dirac/Connes-metric-to-canonical-basis bridge.
"""
import math
import numpy as np


def witnesses(u):
    """Basis order: active p0, kernel q0, neutral n1, n2, active p3, kernel q3."""
    plus = np.zeros((6, 6), dtype=complex)
    minus = np.zeros((6, 6), dtype=complex)
    plus[0, 4] = 1
    plus[4, 0] = 1
    sign = np.array([[-1, 1], [1, -1]])
    for row, i in enumerate([1, 5]):
        for col, j in enumerate([2, 3]):
            plus[i, j] = u[row, col]
            plus[j, i] = np.conj(u[row, col])
            minus[i, j] = sign[row, col] * u[row, col]
            minus[j, i] = np.conj(minus[i, j])
    return plus, minus


def verify(u):
    plus, minus = witnesses(u)
    a, b = (plus + minus) / 2, (plus - minus) / 2
    assert np.allclose(u @ u.conj().T, np.eye(2), atol=1e-11)
    assert np.allclose(plus @ plus, np.eye(6), atol=1e-11)
    assert np.allclose(minus @ minus @ minus, minus, atol=1e-11)
    assert np.allclose(np.linalg.eigvalsh(minus), [-1, -1, 0, 0, 1, 1])
    anorm = np.linalg.norm(a, 2)
    bnorm = np.linalg.norm(b, 2)
    assert np.isclose(anorm, max(0.5, abs(u[0, 1]), abs(u[1, 0])))
    assert np.isclose(bnorm, max(0.5, abs(u[0, 0]), abs(u[1, 1])))
    assert min(anorm, bnorm) <= 1 / math.sqrt(2) + 1e-11
    return float(anorm), float(bnorm)


def main():
    rng = np.random.default_rng(95)
    worst = (0.0, 0.0)
    for theta in np.linspace(0, math.pi / 2, 101):
        u = np.array([[math.cos(theta), math.sin(theta)],
                      [-math.sin(theta), math.cos(theta)]], dtype=complex)
        a, b = verify(u)
        if min(a, b) > min(worst):
            worst = (a, b)
    for _ in range(500):
        z = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
        q, r = np.linalg.qr(z)
        u = q @ np.diag(np.conj(np.diag(r)) / np.abs(np.diag(r)))
        verify(u)
    print("MAN-98: 101 real rotations + 500 complex unitaries passed")
    print(f"Maximum sampled min norm in rotation scan: {min(worst):.12f}")
    print(f"Analytic upper bound 1/sqrt(2): {1/math.sqrt(2):.12f}")


if __name__ == "__main__":
    main()
