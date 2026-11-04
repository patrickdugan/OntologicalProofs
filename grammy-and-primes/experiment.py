"""Finite wheel and twin-prime experiments. Standard library only.

These tests support finite identities; they establish no integer twin-prime
asymptotic, no Riemann hypothesis, and no metaphysical claim.
"""
from math import gcd, isqrt, prod


def primes_through(h: int) -> list[int]:
    return [p for p in range(2, h + 1) if p > 1 and all(p % d for d in range(2, isqrt(p) + 1))]


def primorial(h: int) -> int:
    return prod(primes_through(h))


def wheel_correlation_direct(h: int, gap: int) -> tuple[int, int]:
    m = primorial(h)
    good = sum(gcd(a, m) == 1 and gcd(a + gap, m) == 1 for a in range(m))
    return good, m


def wheel_correlation_crt(h: int, gap: int) -> tuple[int, int]:
    ps = primes_through(h)
    return prod(p - (1 if gap % p == 0 else 2) for p in ps), prod(ps)


def is_prime_64(n: int) -> bool:
    """Deterministic for integers strictly below 2**64."""
    if not (0 <= n < 2**64):
        raise ValueError('is_prime_64 requires 0 <= n < 2**64')
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        a %= n
        if a == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def twin_count(h: int, kmax: int) -> int:
    m = primorial(h)
    if m * kmax + 1 >= 2**64:
        raise ValueError('experiment exceeds certified 64-bit primality range')
    return sum(is_prime_64(m * k - 1) and is_prime_64(m * k + 1)
               for k in range(1, kmax + 1))


def parity_test(h: int, x: int) -> tuple[int, int]:
    """Check the prime indicator recovered from a sieve and Liouville sign."""
    assert x <= h**3
    psmall = primorial(h)
    spf = list(range(x + 1))
    for p in range(2, isqrt(x) + 1):
        if spf[p] == p:
            for multiple in range(p * p, x + 1, p):
                if spf[multiple] == multiple:
                    spf[multiple] = p
    wrong = 0
    survivors = 0
    for n in range(h + 1, x + 1):
        if gcd(n, psmall) != 1:
            continue
        survivors += 1
        t, omega = n, 0
        while t > 1:
            omega += 1
            t //= spf[t]
        assert omega <= 2
        if (omega == 1) != is_prime_64(n):
            wrong += 1
    return wrong, survivors


def run_checks() -> None:
    for h in (2, 3, 5, 7, 11, 13):
        for gap in (1, 2, 4, 6, 10):
            assert wheel_correlation_direct(h, gap) == wheel_correlation_crt(h, gap)
    assert wheel_correlation_direct(5, 2) == (3, 30)
    assert 30 * 4 - 1 == 7 * 17
    assert 30 * 4 + 1 == 11 * 11
    counts = {5: 988, 7: 1016, 11: 900, 13: 735, 17: 663, 19: 595, 23: 525}
    for h, expected in counts.items():
        observed = twin_count(h, 10_000)
        assert observed == expected, (h, observed, expected)
        print(f'H={h:2d}   primorial={primorial(h):>10d}   verified_twin_pairs={observed}')
    wrong, survivors = parity_test(100, 100_000)
    assert wrong == 0
    print(f'Liouville parity verified for {survivors} survivors; disagreements={wrong}')
    print('PASS: CRT wheel, certified 64-bit prime pairs, and cubic-threshold parity')


if __name__ == '__main__':
    run_checks()
