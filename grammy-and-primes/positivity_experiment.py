"""Exact finite tests for weighted reflection positivity.

Standard-library rational arithmetic only. These are synthetic spectra;
no actual zeta zeros or Riemann-Hypothesis estimates are computed.
"""
from __future__ import annotations

import json
from fractions import Fraction as F
from itertools import combinations, product
from typing import Iterator, Sequence


def involutions(n: int) -> Iterator[tuple[int, ...]]:
    """Enumerate all involutions on n labelled points, without duplicates."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    image = list(range(n))

    def generate(free: tuple[int, ...]) -> Iterator[tuple[int, ...]]:
        if not free:
            yield tuple(image)
            return
        a, *rest = free
        image[a] = a
        yield from generate(tuple(rest))
        for b in rest:
            image[a], image[b] = b, a
            yield from generate(tuple(i for i in rest if i != b))
            image[a], image[b] = a, b

    yield from generate(tuple(range(n)))


def validate(tau: Sequence[int], weights: Sequence[F]) -> None:
    n = len(tau)
    if len(weights) != n:
        raise ValueError("weight length must equal spectrum size")
    if any(j < 0 or j >= n for j in tau):
        raise ValueError("reflection has an out-of-range image")
    if any(tau[tau[i]] != i for i in range(n)):
        raise ValueError("reflection must be an involution")
    if any(w <= 0 for w in weights):
        raise ValueError("the theorem requires strictly positive weights")


def quadratic(tau: Sequence[int], weights: Sequence[F], v: Sequence[F]) -> F:
    if not (len(tau) == len(weights) == len(v)):
        raise ValueError("dimensions must agree")
    return sum((weights[i] * v[i] * v[tau[i]] for i in range(len(tau))), F(0))


def symmetric_matrix(tau: Sequence[int], weights: Sequence[F]) -> list[list[F]]:
    n = len(tau)
    matrix = [[F(0) for _ in range(n)] for _ in range(n)]
    for i in range(n):
        matrix[i][tau[i]] += weights[i] / 2
        matrix[tau[i]][i] += weights[i] / 2
    return matrix


def determinant(a: Sequence[Sequence[F]]) -> F:
    """Exact Gaussian elimination, with row-pivot sign tracking."""
    b = [list(row) for row in a]
    n = len(b)
    if any(len(row) != n for row in b):
        raise ValueError("matrix must be square")
    result = F(1)
    for col in range(n):
        pivot = next((r for r in range(col, n) if b[r][col]), None)
        if pivot is None:
            return F(0)
        if pivot != col:
            b[col], b[pivot] = b[pivot], b[col]
            result = -result
        value = b[col][col]
        result *= value
        for r in range(col + 1, n):
            scale = b[r][col] / value
            for c in range(col + 1, n):
                b[r][c] -= scale * b[col][c]
            b[r][col] = F(0)
    return result


def all_principal_minors(a: Sequence[Sequence[F]]) -> list[F]:
    n = len(a)
    return [determinant([[a[i][j] for j in indices] for i in indices])
            for size in range(n + 1) for indices in combinations(range(n), size)]


def run() -> dict[str, object]:
    tally = {"involutions": 0, "weighted_spectra": 0,
             "negative_witnesses": 0, "principal_minor_psd_checks": 0,
             "symmetric_test_vectors": 0}
    size_counts: dict[int, int] = {}
    expected_counts = [1, 1, 2, 4, 10, 26, 76, 232, 764]
    for n in range(9):
        seen = set()
        for tau in involutions(n):
            assert tau not in seen
            seen.add(tau)
            tally["involutions"] += 1
            identity = all(tau[i] == i for i in range(n))
            choices = ([F(1)] * n,
                       [F(i + 1, n + 1) for i in range(n)],
                       [F((i + 1) * (tau[i] + 1)) for i in range(n)])
            for weights in choices:
                validate(tau, weights)
                tally["weighted_spectra"] += 1
                for a in range(n):
                    if tau[a] == a:
                        continue
                    v = [F(0)] * n
                    v[a], v[tau[a]] = F(1), F(-1)
                    q = quadratic(tau, weights, v)
                    assert q == -weights[a] - weights[tau[a]] < 0
                    tally["negative_witnesses"] += 1
                if n <= 5:
                    minors = all_principal_minors(symmetric_matrix(tau, weights))
                    assert all(m >= 0 for m in minors) == identity
                    tally["principal_minor_psd_checks"] += 1
                    for values in product((-1, 0, 1), repeat=n):
                        if all(values[i] == values[tau[i]] for i in range(n)):
                            assert quadratic(tau, weights, values) >= 0
                            tally["symmetric_test_vectors"] += 1
        size_counts[n] = len(seen)
        assert len(seen) == expected_counts[n]
    swap, weights = (1, 0), [F(1), F(1)]
    assert quadratic(swap, weights, [F(1), F(1)]) == 2
    assert quadratic(swap, weights, [F(1), F(-1)]) == -2
    assert sum(x * x for x in [F(1), F(-1)]) == 2
    # Zero weights exhibit the failure when strict positivity is removed.
    assert quadratic(swap, [F(0), F(0)], [F(1), F(-1)]) == 0
    for bad_tau, bad_weights in [((1, 2, 0), [F(1)] * 3),
                                 ((1, 0), [F(0), F(1)]),
                                 ((2, 0), [F(1), F(1)])]:
        try:
            validate(bad_tau, bad_weights)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid theorem hypothesis accepted")
    return {"status": "PASS", "scope": "synthetic finite rational spectra",
            "counts_by_size": size_counts, **tally,
            "swap_symmetric_q": 2, "swap_antisymmetric_q": -2,
            "ordinary_norm_squared": 2,
            "actual_zeta_zeros_used": False}


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True, indent=2))
