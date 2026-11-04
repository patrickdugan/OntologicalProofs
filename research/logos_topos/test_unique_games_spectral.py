"""Independent exact finite checks for LTR-UG-01, without third-party libraries."""
from fractions import Fraction
from itertools import product
import unittest


def score(edges, assignment):
    return sum(assignment[v] == (assignment[u] ^ shift) for u, v, shift in edges)


def projection_norm(edges, vertices, bits):
    """Norm of the finite diagonal mean of edge-satisfaction projections."""
    if not edges:
        return Fraction(1)
    # Each assignment is a basis point of the Stone space K^V.
    return max(Fraction(score(edges, a), len(edges))
               for a in product(range(1 << bits), repeat=vertices))


def gauge(edges, p):
    return tuple((u, v, shift ^ p[u] ^ p[v]) for u, v, shift in edges)


def curvature_for_cycle(edges):
    """For F_2^s translations, cycle orientation signs disappear."""
    return 0 if not edges else __import__("functools").reduce(
        int.__xor__, (c for _, _, c in edges), 0)


class UniqueGamesSpectralTests(unittest.TestCase):
    def test_frustrated_four_cycle(self):
        edges = ((0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 0, 1))
        self.assertEqual(curvature_for_cycle(edges), 1)
        self.assertEqual(projection_norm(edges, 4, 1), Fraction(3, 4))
        self.assertEqual(Fraction(1) - projection_norm(edges, 4, 1),
                         Fraction(1, 4))

    def test_gauge_and_curvature_for_every_four_cycle(self):
        pattern = ((0, 1), (1, 2), (2, 3), (3, 0))
        for shifts in product(range(4), repeat=4):
            edges = tuple((u, v, c) for (u, v), c in zip(pattern, shifts))
            hol = curvature_for_cycle(edges)
            expected = Fraction(1 if hol == 0 else 3, 1 if hol == 0 else 4)
            self.assertEqual(projection_norm(edges, 4, 2), expected)
            p = (1, 2, 3, 0)
            transformed = gauge(edges, p)
            self.assertEqual(curvature_for_cycle(transformed), hol)
            self.assertEqual(projection_norm(transformed, 4, 2), expected)

    def test_one_hot_energy_and_empty_graph(self):
        edge = ((0, 1, 1),)
        self.assertEqual(projection_norm(edge, 2, 1), 1)
        self.assertEqual(projection_norm((), 2, 1), 1)


if __name__ == "__main__":
    unittest.main()
