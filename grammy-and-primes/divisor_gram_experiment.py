"""Exact divisor-incidence Gram matrices and finite Mobius inversion.

This constructs a positive arithmetic form independently of RH.
No equality with the Weil functional is assumed or numerically asserted.
"""
from __future__ import annotations

import json
from fractions import Fraction as F
from positivity_experiment import determinant

Matrix = list[list[F]]


def mobius(n: int) -> int:
    if n < 1:
        raise ValueError("Mobius input must be positive")
    sign, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


def transpose(a: Matrix) -> Matrix:
    return [list(row) for row in zip(*a)]


def multiply(a: Matrix, b: Matrix) -> Matrix:
    if not a or not b or len(a[0]) != len(b):
        raise ValueError("incompatible nonempty matrix dimensions")
    return [[sum((x * y for x, y in zip(row, col)), F(0))
             for col in transpose(b)] for row in a]


def run() -> dict[str, object]:
    energy_checks = 0
    for n in range(1, 17):
        z = [[F(int(j % d == 0)) for j in range(1, n + 1)]
             for d in range(1, n + 1)]
        m = [[F(mobius(j // d) if j % d == 0 else 0)
              for j in range(1, n + 1)] for d in range(1, n + 1)]
        identity = [[F(int(i == j)) for j in range(n)] for i in range(n)]
        k = multiply(transpose(z), z)
        assert multiply(z, m) == identity
        assert multiply(m, z) == identity
        assert multiply(multiply(transpose(m), k), m) == identity
        assert determinant(z) == determinant(k) == 1
        vectors = [[F(1)] * n,
                   [F((-1) ** j) for j in range(n)],
                   [F(int(j == 0) - int(j == n - 1)) for j in range(n)]]
        for v in vectors:
            features = [sum((a * b for a, b in zip(row, v)), F(0)) for row in z]
            energy = sum((x * x for x in features), F(0))
            quadratic = sum((v[i] * k[i][j] * v[j]
                             for i in range(n) for j in range(n)), F(0))
            assert features[0] == sum(v)
            assert energy == quadratic >= 0
            if any(v):
                assert energy > 0
            energy_checks += 1
    return {"status": "PASS", "matrix_sizes": list(range(1, 17)),
            "two_sided_mobius_inverse_checks": 32,
            "gram_congruence_checks": 16, "determinant_checks": 32,
            "exact_energy_checks": energy_checks,
            "two_point_gram_matrix": [[1, 1], [1, 2]],
            "two_point_alternating_energy": 1,
            "weil_form_identified": False}


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True, indent=2))
