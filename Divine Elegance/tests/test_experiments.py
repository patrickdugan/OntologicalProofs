import unittest
from experiments import (e01_salvation_models as modal, e02_global_gluing as glue,
                         e03_nineteen as nineteen, e04_constrained_elegance as mdl,
                         e05_relevant_invariance as invariance,
                         e06_defensive_action_gate as gate)

class TestTheologicalModelFixtures(unittest.TestCase):
    def test_salvation_counts(self):
        a=modal.count_models()
        self.assertEqual([a['base'],a['one_way_S_implies_not_I'],
                         a['exhaustion_not_I_implies_S'],a['equivalence']],[10,9,6,5])
    def test_global_parity_counterexample(self):
        tr=[([0,1],0),([1,2],0),([0,2],1)]
        self.assertFalse(glue.is_consistent(3,tr))
        for i in range(3):self.assertTrue(glue.is_consistent(3,tr[:i]+tr[i+1:]))
    def test_random_parity_sweep(self):
        res=glue.cycle_experiment(trials=2000)
        self.assertEqual([v['independent_cycles'] for v in res['sweep']],list(range(7)))
    def test_any_nineteen_letter_input(self):
        res=nineteen.check(samples=250)
        self.assertEqual([d['score'] for d in res['preselected_examples']],[225,228])
    def test_constraints_before_compression(self):
        res=mdl.evaluate()
        self.assertNotEqual(res['naive_winner'],res['constrained_winner'])
    def test_relevant_relabeling(self):
        res=invariance.evaluate()
        self.assertEqual(res['principled_label_swap_failures'],0)
        self.assertGreater(res['proxy_label_swap_failures'],0)
    def test_defensive_gate(self):
        res=gate.run()
        self.assertEqual([r['status'] for r in res['cases']].count('HOLD'),1)

if __name__=='__main__': unittest.main()
