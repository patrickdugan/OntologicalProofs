"""Finite audits for LTR. Enumeration checks complement the Lean proofs.

Run: python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
No third-party packages are required.
"""
from itertools import product
import unittest


def assignments(n):
    return tuple(product((False, True), repeat=n))


def powerset(values):
    values = tuple(values)
    for mask in range(1 << len(values)):
        yield frozenset(x for i, x in enumerate(values) if mask & (1 << i))


def triangle_edges(x):
    return (x[0] == x[1], x[1] == x[2], x[2] != x[0])


def cycle_solutions(flips):
    n = len(flips)
    if not n:
        raise ValueError('A cycle needs at least one edge.')
    return tuple(x for x in assignments(n)
                 if all(x[(i + 1) % n] == (x[i] != flips[i]) for i in range(n)))


class FiniteNetworkTests(unittest.TestCase):
    def test_truth_loci_and_independence(self):
        universe = tuple(range(4))
        for models in powerset(universe):
            for sentence in powerset(universe):
                locus = models & sentence
                entails = models <= sentence
                refutes = models.isdisjoint(sentence)
                self.assertEqual(locus == models, entails)
                self.assertEqual(not locus, refutes)
                self.assertEqual((not entails and not refutes), bool(locus) and locus != models)

    def test_triangle_each_pair_but_no_global(self):
        points = assignments(3)
        self.assertEqual(sum(all(triangle_edges(x)) for x in points), 0)
        for i, j in product(range(3), repeat=2):
            self.assertTrue(any(triangle_edges(x)[i] and triangle_edges(x)[j] for x in points))
        for i in range(3):
            for vertex in range(3):
                self.assertEqual({x[vertex] for x in points if triangle_edges(x)[i]}, {False, True})

    def test_cycle_holonomy_parity(self):
        for n in range(1, 8):
            for flips in assignments(n):
                expected = 2 if sum(flips) % 2 == 0 else 0
                self.assertEqual(len(cycle_solutions(flips)), expected)

    def test_surjectivity_exactly_reflects_coverage(self):
        for nx in range(0, 5):
            for ny in range(1, 4):
                for f in product(range(ny), repeat=nx):
                    onto = set(f) == set(range(ny))
                    all_coverage_reflected = True
                    for u in powerset(range(ny)):
                        preimage = {i for i, y in enumerate(f) if y in u}
                        covers_x = len(preimage) == nx
                        covers_y = len(u) == ny
                        all_coverage_reflected &= not covers_x or covers_y
                        if onto:
                            self.assertEqual(covers_x, covers_y)
                            self.assertEqual(not preimage, not u)
                            self.assertEqual(bool(preimage) and not covers_x, bool(u) and not covers_y)
                    self.assertEqual(all_coverage_reflected, onto)

    def test_nonconservative_gluing_can_decide_a_sentence(self):
        local_states = {False, True}
        global_states = {True}
        truth_locus = {True}
        self.assertTrue(truth_locus and truth_locus != local_states)
        self.assertEqual(truth_locus & global_states, global_states)

    def test_bijective_transport_alone_is_insufficient(self):
        flip = {False: True, True: False}
        self.assertEqual(set(flip.values()), set(flip))
        self.assertFalse(any(flip[x] == x for x in flip))


if __name__ == '__main__':
    unittest.main(verbosity=2)
