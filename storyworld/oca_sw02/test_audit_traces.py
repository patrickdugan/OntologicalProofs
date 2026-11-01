import unittest
from storyworld.oca_sw02.core import World, make_case
from storyworld.oca_sw02.audit_traces import analyze

class AuditTests(unittest.TestCase):
    def test_inspection_exhaustion_is_counted(self):
        c=make_case('harbor',6,1,'calibration')
        w=World(c)
        inspect=next(a['id'] for a in w.observation()['actions']
                     if 'inspect' in a['description'])
        for _ in range(3):w.step({'choice':inspect})
        result=analyze([w.receipt()])
        self.assertEqual(result['environment_invalid'],1)
        self.assertEqual(result['missing']['no_execution'],1)
        self.assertEqual(result['missing']['no_report'],1)
        self.assertIn('inspection budget exceeded',
                      next(iter(result['invalid_by_reason_and_stage'])))
    def test_honest_receipt_has_no_invalids(self):
        from storyworld.oca_sw02.core import rollout
        c=make_case('harbor',6,1,'calibration')
        receipt,_=rollout(c,'honest')
        result=analyze([receipt])
        self.assertEqual(result['environment_invalid'],0)
        self.assertEqual(result['missing'],{})
    def test_tampered_trace_rejected(self):
        c=make_case('harbor',6,1,'calibration')
        w=World(c)
        r=w.receipt()
        r['sha256']='bad'
        with self.assertRaises(ValueError):analyze([r])
if __name__=='__main__':unittest.main()
