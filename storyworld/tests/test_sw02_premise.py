import unittest
from storyworld.oca_sw02.premise import (GROUNDING,QUESTIONS,REQUIRED,make_case,fixtures,
    verdict,paired_withdrawal_count)

class PremiseTest(unittest.TestCase):
    def test_complete_conditional_grounding(self):
        x=make_case('unique_root',None)
        self.assertEqual(x['answer']['verdict'],'conditionally_entailed')
    def test_every_grounding_premise_load_bearing(self):
        for premise in GROUNDING:
            with self.subTest(premise=premise):
                x=make_case('unique_root',premise)
                self.assertEqual(x['answer']['verdict'],'insufficient_premises')
    def test_moral_bridge_independent(self):
        x=make_case('moral_duty','value_bridge')
        self.assertTrue(all(x['premises'][p] for p in GROUNDING))
        self.assertEqual(x['answer']['verdict'],'insufficient_premises')
    def test_personhood_requires_bridge(self):
        x=make_case('personal_deity','personal_bridge')
        self.assertEqual(x['answer']['verdict'],'insufficient_premises')
    def test_guidance_authentication_and_reliability(self):
        for missing in REQUIRED['guidance_claim']:
            self.assertEqual(make_case('guidance_claim',missing)['answer']['verdict'],'insufficient_premises')
    def test_no_falsehood_label(self):
        for item in fixtures():
            self.assertIn(item['answer']['verdict'],('conditionally_entailed','insufficient_premises'))
            self.assertNotIn('false',item['public_prompt'].split('Claim:')[-1].lower())
    def test_paired_premise_changes(self):
        rows=fixtures()
        self.assertEqual(len(rows),4*sum(1+len(REQUIRED[q]) for q in QUESTIONS))
        self.assertEqual(set(paired_withdrawal_count(rows)),set(QUESTIONS))
    def test_deterministic_permutation(self):
        self.assertEqual(fixtures(11),fixtures(11))
        self.assertNotEqual(fixtures(11),fixtures(29))
    def test_irrelevant_withdrawal_rejected(self):
        with self.assertRaises(ValueError):make_case('unique_root','source_reliable')

if __name__=='__main__':unittest.main()
