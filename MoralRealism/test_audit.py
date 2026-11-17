"""Independent controls for the finite audit. No empirical model conclusions."""
from fractions import Fraction as F
import unittest
from audit import (audit_all, audit_execution, contract_flags, decode_possible,
                   edges_from_mask, posterior, reachable_states, unsafe_reachable_effect)


class MoralRealismTests(unittest.TestCase):
    def test_all_two_state_systems(self):
        result = audit_execution()
        self.assertEqual(result["systems"], 4 * 4 * 256 * 16 * 16)
        self.assertEqual(result["unsafe_contracts"], 0)
        self.assertGreater(result["contracts_with_reachable_effect"], 0)

    def test_each_premise_has_a_countermodel(self):
        witnesses = audit_execution()["premise_deletion_witnesses"]
        self.assertEqual(set(witnesses), {"starts", "preserves", "mediation", "sound"})
        for missing, w in witnesses.items():
            with self.subTest(missing=missing):
                edges = edges_from_mask(w["edge_mask"])
                actual = contract_flags(w["initial"], w["invariant"], edges, w["gate"], w["lawful"])
                self.assertEqual(actual, w["holds"])
                self.assertFalse(actual[missing])
                self.assertEqual(sum(actual.values()), 3)
                self.assertTrue(unsafe_reachable_effect(w["initial"], edges, w["lawful"]))

    def test_reachability_fixed_point(self):
        self.assertEqual(reachable_states(1, ((0, 0, 1), (1, 1, 0))), 3)
        self.assertEqual(reachable_states(0, ((0, 0, 1),)), 0)

    def test_unreachable_bad_effect_does_not_fail_property(self):
        self.assertFalse(unsafe_reachable_effect(1, ((1, 0, 1),), 0))
        self.assertTrue(unsafe_reachable_effect(2, ((1, 0, 1),), 0))

    def test_self_update_can_break_invariant(self):
        edges = ((0, 1, 1), (1, 0, 1))
        flags = contract_flags(1, 1, edges, 0b0110, 0b0010)
        self.assertEqual(flags, {"starts": True, "preserves": False,
                                 "mediation": True, "sound": True})
        self.assertTrue(unsafe_reachable_effect(1, edges, 0b0010))

    def test_collision(self):
        self.assertFalse(decode_possible((0, 0), (0, 1)))
        self.assertTrue(decode_possible((0, 1), (0, 1)))

    def test_unused_view_is_harmless(self):
        self.assertTrue(decode_possible((0, 0), (1, 1)))

    def test_invalid_view_input(self):
        for view, duty in [((), ()), ((0,), ()), ((2,), (1,))]:
            with self.assertRaises(ValueError):
                decode_possible(view, duty)

    def test_guidance_exact_update(self):
        self.assertEqual(posterior(F(1, 2), F(3, 4), F(1, 4)), F(3, 4))
        self.assertEqual(posterior(F(1, 2), F(1, 4), F(3, 4)), F(1, 4))

    def test_equal_likelihoods_do_not_update(self):
        self.assertEqual(posterior(F(2, 3), F(1, 7), F(1, 7)), F(2, 3))

    def test_zero_event_rejected(self):
        for prior, hit, false_alarm in [(F(1, 2), F(0), F(0)), (F(0), F(1), F(0)),
                                        (F(1), F(0), F(1))]:
            with self.assertRaises(ValueError):
                posterior(prior, hit, false_alarm)

    def test_invalid_probability_rejected(self):
        with self.assertRaises(ValueError):
            posterior(F(-1), F(1), F(1))
        with self.assertRaises(TypeError):
            posterior(0.5, F(1), F(1))

    def test_duplicate_evidence_requires_dependence_model(self):
        once = posterior(F(1, 2), F(3, 4), F(1, 4))
        # The same event observed twice has conditional likelihood one, given itself.
        repeated_same_event = posterior(once, F(1), F(1))
        wrongly_independent = posterior(once, F(3, 4), F(1, 4))
        self.assertEqual(repeated_same_event, once)
        self.assertNotEqual(wrongly_independent, once)

    def test_knowledge_can_coexist_with_violation(self):
        duty, judgment = True, True
        action = {True: True, False: False}
        self.assertEqual(duty, judgment)
        self.assertEqual(action[True], duty)
        self.assertNotEqual(action[False], duty)

    def test_zero_oversight_gap_can_hide_uniform_violation(self):
        action = {True: False, False: False}
        self.assertEqual(action[True], action[False])
        self.assertNotEqual(action[False], True)

    def test_small_honesty_penalty_can_be_outweighed(self):
        honest_reward, dishonest_reward, penalty = 10, 12, 1
        self.assertGreater(dishonest_reward - penalty, honest_reward)

    def test_tied_maximum_needs_strict_priority(self):
        lawful = (True, False)
        scores = (1, 1)
        self.assertEqual(scores[1], max(scores))
        self.assertFalse(lawful[1])

    def test_counts_and_reproducibility(self):
        first, second = audit_all(), audit_all()
        self.assertEqual(first, second)
        self.assertEqual(first["information"]["view_duty_pairs"], 256)
        self.assertEqual(first["guidance"]["positive_event_cases"], 1080)
        self.assertEqual(first["motivation"]["candidate_cases"], 5184)

    def test_bad_edge_mask_rejected(self):
        for mask in (-1, 256, True):
            with self.assertRaises(ValueError):
                edges_from_mask(mask)


if __name__ == "__main__":
    unittest.main()
