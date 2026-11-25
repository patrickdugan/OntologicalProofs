"""Finite-field irreducibility checks of x^(3^m)-a over F_7.

Rabin's criterion via polynomial Frobenius, for the test degrees 3^m.
This is a small-degree computational check, not a computation at Graham degree.
"""
P = 7


def trim(a: list[int]) -> list[int]:
    while a and a[-1] % P == 0:
        a.pop()
    return a


def rem(a: list[int], f: list[int]) -> list[int]:
    r = [x % P for x in a]
    f = trim(f.copy())
    assert f and f[-1] == 1, 'monic modulus required'
    while len(r) >= len(f):
        c = r[-1]
        if c:
            start = len(r) - len(f)
            for j, fj in enumerate(f):
                r[start + j] = (r[start + j] - c * fj) % P
        trim(r)
    return r


def multiply(a: list[int], b: list[int], f: list[int]) -> list[int]:
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i + j] = (out[i + j] + ai * bj) % P
    return rem(out, f)


def pow_mod(a: list[int], exponent: int, f: list[int]) -> list[int]:
    acc = [1]
    while exponent:
        if exponent % 2:
            acc = multiply(acc, a, f)
        exponent //= 2
        if exponent:
            a = multiply(a, a, f)
    return acc


def gcd_monic(a: list[int], b: list[int]) -> list[int]:
    a, b = trim(a.copy()), trim(b.copy())
    while b:
        inv = pow(b[-1], P - 2, P)
        normalized = [(c * inv) % P for c in b]
        a, b = b, rem(a, normalized)
    if a:
        inv = pow(a[-1], P - 2, P)
        a = [(c * inv) % P for c in a]
    return a


def is_irreducible_power3(n: int, a: int) -> bool:
    assert n >= 3 and n % 3 == 0
    f = [(-a) % P] + [0] * (n - 1) + [1]
    current = [0, 1]
    for j in range(1, n + 1):
        current = pow_mod(current, P, f)
        if j == n // 3:
            difference = current.copy()
            difference[1] = (difference[1] - 1) % P
            if gcd_monic(f, trim(difference)) != [1]:
                return False
    return trim(current) == [0, 1]


def main() -> None:
    assert is_irreducible_power3(3, 2)
    assert not is_irreducible_power3(3, 1)
    for m in (1, 2, 3, 4):
        n = 3**m
        for a in (2, 3, 4, 5):
            assert is_irreducible_power3(n, a), (n, a)
        print(f'PASS: four irreducible polynomials of degree {n} over F7')
    print('PASS: all finite-degree binomial tests, with reducible control')


if __name__ == '__main__':
    main()
