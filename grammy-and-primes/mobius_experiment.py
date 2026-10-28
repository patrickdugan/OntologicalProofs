"""Finite Mertens summatory-function checkpoints; no RH proof.

Compare against published Mertens function values. This does not test an
infinite O(x**(1/2 + epsilon)) asymptotic.
"""
from math import sqrt

CHECKPOINTS = {10: -1, 100: 1, 1_000: 2, 10_000: -23, 100_000: -48, 1_000_000: 212}


def mobius_up_to(n: int) -> list[int]:
    mu = [1] * (n + 1)
    mu[0] = 0
    is_prime = bytearray(b'\x01') * (n + 1)
    is_prime[:2] = b'\x00\x00'
    for p in range(2, n + 1):
        if not is_prime[p]:
            continue
        for multiple in range(p, n + 1, p):
            mu[multiple] *= -1
        for multiple in range(p * p, n + 1, p * p):
            mu[multiple] = 0
        for multiple in range(p * p, n + 1, p):
            is_prime[multiple] = 0
    return mu


def main() -> None:
    mu = mobius_up_to(max(CHECKPOINTS))
    total = 0
    print('x\tM(x)\tM(x)/sqrt(x)')
    for x in range(1, max(CHECKPOINTS) + 1):
        total += mu[x]
        if x in CHECKPOINTS:
            assert total == CHECKPOINTS[x], (x, total, CHECKPOINTS[x])
            print(f'{x}\t{total}\t{total / sqrt(x):+.6f}')
    assert mu[1] == 1 and mu[2] == -1 and mu[4] == 0 and mu[30] == -1
    print('PASS: Möbius sieve and six published Mertens checkpoints')


if __name__ == '__main__':
    main()
