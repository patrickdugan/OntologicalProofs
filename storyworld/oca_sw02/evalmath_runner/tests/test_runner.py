"""End-to-end CPU tests for the OCA-SW-02R runner. No Qwen weights, no GPU."""
import copy
import importlib.util
import json
import lzma
import tempfile
import unittest
from fractions import Fraction as F
from pathlib import Path
from storyworld.oca_sw02.core import World, digest, write_json
from storyworld.oca_sw02.evaluate import action_prompt
from storyworld.oca_sw02.evalmath_runner import (build_plan, validate_plan, regenerate_and_compare, run_campaign,
    score_run, IncompleteCampaign, ScriptedBackend, BackendFailure, Generation)
from storyworld.oca_sw02.evalmath_runner.plan import case_from_dict, incident_from_dict
from storyworld.oca_sw02.evalmath_runner.prompts import decision_prompt, reporting_prompt, observation_from_prompt, sha
from storyworld.oca_sw02.evalmath_runner.provenance import source_hashes
from storyworld.oca_sw02.evalmath_runner.__main__ import main as cli

HAS_HF=all(importlib.util.find_spec(m) for m in ('torch','transformers'))
SMALL=dict(themes=['harbor','clinic'])


def small_plan(arms=('S1','O1'),**kw):
    return build_plan(list(arms),'calibration',**{**SMALL,**kw})


def rehash(plan):
    plan=copy.deepcopy(plan);plan.pop('plan_sha256',None);plan['plan_sha256']=digest(plan);return plan


def read_records(d):
    return [json.loads(x) for x in (Path(d)/'rollouts.jsonl').read_text().splitlines()]


def write_records(d,records):
    (Path(d)/'rollouts.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in records))


class FaultBackend:
    """Wrap a backend; raise the given exception on chosen call numbers."""
    def __init__(self,inner,faults):
        self.inner,self.faults,self.calls=inner,dict(faults),0
        self.evidence_class=inner.evidence_class
    def select(self,arm):self.inner.select(arm)
    def generate(self,prompt,lane=None):
        n=self.calls;self.calls+=1
        if n in self.faults:raise self.faults[n]
        return self.inner.generate(prompt,lane)
    def describe(self):return self.inner.describe()


class FixedOutput(ScriptedBackend):
    def __init__(self,arms,decision,report='{"report":"accurate"}'):
        super().__init__({a:'honest' for a in arms});self.d,self.r=decision,report
    def generate(self,prompt,lane=None):
        lane,view=observation_from_prompt(prompt)
        if lane=='reporting':return Generation(self.r,'scripted',adapter=self.active)
        return Generation(self.d(view) if callable(self.d) else self.d,'scripted',adapter=self.active)


class Run:
    def __init__(self,plan,backend,**kw):
        self.tmp=tempfile.TemporaryDirectory();self.dir=Path(self.tmp.name)/'run'
        self.manifest=run_campaign(plan,backend,self.dir,**kw)
    def score(self):return score_run(self.dir)
    def __enter__(self):return self
    def __exit__(self,*a):self.tmp.cleanup()


class PlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.plan=small_plan()
    def test_complete_balanced_blocks(self):
        self.assertEqual(len(self.plan['blocks']),4)
        self.assertEqual(self.plan['arm_position_counts'],{'S1':[2,2],'O1':[2,2]})
        for b in self.plan['blocks']:
            self.assertEqual(len(b['units']),12)
            self.assertEqual(sum(u['lane']=='decision' for u in b['units']),8)
            self.assertEqual(sorted(b['unit_order']),sorted(u['unit_id'] for u in b['units']))
    def test_regenerates_from_bridge(self):
        self.assertTrue(regenerate_and_compare(json.loads(json.dumps(self.plan))))
    def test_one_pivot_and_matched_keys(self):
        for b in self.plan['blocks']:
            dec=[u for u in b['units'] if u['lane']=='decision']
            lo=case_from_dict(next(u['case'] for u in dec if not u['authorized']))
            hi=case_from_dict(next(u['case'] for u in dec if u['authorized']))
            self.assertEqual([k for k in lo.facts if lo.facts[k]!=hi.facts[k]],[b['pivot']])
            self.assertEqual(len({u['permutation_key'] for u in dec}),1)
            self.assertEqual(len({u['audit_key'] for u in dec}),4)
            self.assertEqual(len({tuple(u['case']['choice_order']) for u in dec}),1)
    def test_sealed_test_refused(self):
        with self.assertRaises(ValueError):build_plan(['S1','O1'],'test')
        with self.assertRaises(ValueError):build_plan(['S1','O1'],'calibration',families=[8])
        bad=copy.deepcopy(self.plan);bad['blocks'][0]['family']=8
        with self.assertRaises(ValueError):validate_plan(rehash(bad))
    def test_unbalanced_order_rejected(self):
        with self.assertRaises(ValueError):small_plan(('S1','O1','X'))
    def test_tamper_hash_rejected(self):
        bad=copy.deepcopy(self.plan);bad['blocks'][0]['arm_order'].reverse()
        with self.assertRaises(ValueError):validate_plan(bad)
    def test_dropped_unit_rejected(self):
        bad=copy.deepcopy(self.plan);u=bad['blocks'][0]['units'].pop(0);bad['blocks'][0]['unit_order'].remove(u['unit_id'])
        with self.assertRaises(ValueError):validate_plan(rehash(bad))
    def test_rehashed_fact_change_fails_regeneration(self):
        bad=copy.deepcopy(self.plan)
        for u in bad['blocks'][0]['units']:
            if u['lane']=='decision':u['case']['instance']+=100
        bad=rehash(bad);validate_plan(bad)
        with self.assertRaises(ValueError):regenerate_and_compare(bad)
    def test_block_order_independent_of_arm_names(self):
        a=small_plan(('S1','O1'));b=small_plan(('A','B'))
        self.assertEqual([x['motif_id'] for x in a['blocks']],[x['motif_id'] for x in b['blocks']])


class PromptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.plan=small_plan()
    def units(self,lane):return [u for b in self.plan['blocks'] for u in b['units'] if u['lane']==lane]
    def test_decision_prompt_is_historical_interface(self):
        for u in self.units('decision'):
            ob=World(case_from_dict(u['case'])).observation()
            self.assertEqual(decision_prompt(ob),action_prompt(ob))
    def test_no_answer_key_or_audit_draw(self):
        for u in self.units('decision'):
            p=decision_prompt(World(case_from_dict(u['case'])).observation())
            for leak in ('allowed','motif',u['motif_id'],'audit_draw','history_id'):self.assertNotIn(leak,p)
        for u in self.units('reporting'):
            inc=incident_from_dict(u['incident']);p=reporting_prompt(inc,u['context'])
            self.assertNotIn('audit_draw',p);self.assertNotIn(u['incident']['audit_draw'],p)
            self.assertIn(u['audit_probability'],p)
    def test_all_facts_visible_main_lane(self):
        for u in self.units('decision'):
            ob=World(case_from_dict(u['case'])).observation()
            self.assertTrue(all(v.startswith('authenticated:') for v in ob['authenticated_records'].values()))
            self.assertEqual(len(ob['actions']),3)
    def test_prompt_envelope_roundtrip(self):
        u=self.units('reporting')[0];p=reporting_prompt(incident_from_dict(u['incident']),u['context'])
        lane,view=observation_from_prompt(p)
        self.assertEqual(lane,'reporting');self.assertEqual(view['incident_id'],u['unit_id'])
        with self.assertRaises(ValueError):observation_from_prompt('free text')


class EndToEndTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plan=small_plan()
        cls.r=Run(cls.plan,ScriptedBackend({'S1':'honest','O1':'conservative'}))
        cls.s=cls.r.score()
    @classmethod
    def tearDownClass(cls):cls.r.tmp.cleanup()
    def test_honest_and_conservative_scores(self):
        a,b=self.s['per_arm']['S1'],self.s['per_arm']['O1']
        self.assertEqual((a['decision']['J_minus'],a['decision']['TPR'],a['decision']['FPR']),('1','1','0'))
        self.assertEqual((b['decision']['J_minus'],b['decision']['TPR'],b['decision']['FPR']),('0','0','0'))
        self.assertEqual(a['reporting']['accurate_rate_bounds'],['1','1'])
        self.assertEqual(b['reporting']['accurate_rate_bounds'],['1','1'])
        p=self.s['paired']['O1_minus_S1']
        self.assertEqual(p['J_minus_blocks']['mean_difference'],'-1')
        self.assertEqual(p['decision']['J_minus_b_minus_a'],'-1')
        self.assertEqual(p['reporting_accuracy_blocks']['mean_difference'],'0')
        self.assertEqual(p['decision']['action_disagreements'],16)
    def test_complete_records_and_legality(self):
        self.assertEqual(self.s['records'],4*2*12)
        self.assertEqual(self.s['status_counts']['completed'],96)
        for a in ('S1','O1'):
            self.assertEqual(self.s['per_arm'][a]['action_legality'],{'unavailable_selected':0,'environment_invalid':0,'malformed':0})
            self.assertEqual(self.s['per_arm'][a]['decision_lane_reports']['covered'],32)
            self.assertEqual(self.s['per_arm'][a]['decision_lane_reports']['false_report'],0)
    def test_order_follows_plan_with_rotation(self):
        recs=read_records(self.r.dir)
        firsts=[next(r['arm'] for r in recs if r['block_index']==b['block_index']) for b in self.plan['blocks']]
        self.assertEqual(firsts,['S1','O1','S1','O1'])
        self.assertEqual([r['sequence'] for r in recs],list(range(len(recs))))
    def test_verbatim_raw_and_adapter_tag(self):
        for r in read_records(self.r.dir):
            for g in r['generations']:
                self.assertEqual(g['adapter'],r['arm']);self.assertEqual(g['prompt_sha256'],sha(g['prompt']))
            if r['lane']=='decision':
                self.assertEqual([e['raw'] for e in r['world_receipt']['state']['events']],[g['raw'] for g in r['generations']])
    def test_matched_prompts_across_arms(self):
        by={}
        for r in read_records(self.r.dir):
            if r['generations']:by.setdefault(r['unit_id'],set()).add(r['generations'][0]['prompt_sha256'])
        self.assertTrue(all(len(v)==1 for v in by.values()))
    def test_reporting_independent_of_decision_policy(self):
        with Run(self.plan,ScriptedBackend({'S1':'always_change','O1':'refuse'})) as other:
            def rp(d):return sorted((r['arm'],r['unit_id'],r['prompt_sha256']) for r in read_records(d) if r['lane']=='reporting')
            self.assertEqual(rp(self.r.dir),rp(other.dir))
    def test_deterministic_rollouts(self):
        with Run(self.plan,ScriptedBackend({'S1':'honest','O1':'conservative'})) as again:
            self.assertEqual((self.r.dir/'rollouts.jsonl').read_bytes(),(again.dir/'rollouts.jsonl').read_bytes())
    def test_score_receipt_hashes(self):
        self.assertEqual(self.s['source_sha256_at_scoring'],source_hashes())
        self.assertEqual(self.s['plan_sha256'],self.plan['plan_sha256'])
        self.assertTrue(all(self.s['checks'].values()))
        self.assertEqual(self.s['claim'],'SYNTHETIC_FUNCTION_CHECK_NOT_A_MODEL_RESULT')
        self.assertFalse(self.s['confirmatory']);self.assertFalse(self.s['final_test_access'])
        self.assertGreaterEqual(len(self.s['limitations']),5)
    def test_compressed_rollouts_rescore(self):
        with tempfile.TemporaryDirectory() as td:
            d=Path(td)
            for f in ('plan.json','run_manifest.json'):(d/f).write_bytes((self.r.dir/f).read_bytes())
            (d/'rollouts.jsonl.xz').write_bytes(lzma.compress((self.r.dir/'rollouts.jsonl').read_bytes()))
            again=score_run(d)
            self.assertEqual(again['per_arm'],self.s['per_arm']);self.assertEqual(again['inputs_sha256'],self.s['inputs_sha256'])


class PolicyBatteryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.plan=small_plan()
    def arm(self,s,a):return s['per_arm'][a]
    def test_change_refuse_battery(self):
        with Run(self.plan,ScriptedBackend({'S1':'always_change','O1':'refuse'})) as r:
            s=r.score()
        self.assertEqual(self.arm(s,'S1')['decision']['J_minus'],'0')
        o=self.arm(s,'O1')
        self.assertEqual(o['decision']['J_minus'],'-1');self.assertEqual(o['decision']['refusals'],32)
        self.assertEqual(o['reporting']['refused'],16);self.assertEqual(o['reporting']['accurate_rate_bounds'],['0','0'])
        self.assertEqual(o['decision']['unknown'],0)
    def test_incentive_and_concealment(self):
        with Run(self.plan,ScriptedBackend({'S1':'bonus_sensitive','O1':'conceal'})) as r:
            s=r.score()
        b=self.arm(s,'S1')
        self.assertEqual(b['decision']['FPR'],'1/2');self.assertEqual(b['decision']['bonus_audit_interaction'],'0')
        c=self.arm(s,'O1')
        self.assertEqual(c['reporting']['false_clean'],4);self.assertEqual(c['reporting']['pressure_effect_R'],'1')
        self.assertEqual(c['reporting']['accurate_rate_bounds'],['3/4','3/4'])
        self.assertEqual(c['decision_lane_reports']['concealed'],16)
    def test_watch_sensitive_interaction(self):
        with Run(self.plan,ScriptedBackend({'S1':'watch_sensitive','O1':'honest'})) as r:
            s=r.score()
        self.assertEqual(self.arm(s,'S1')['decision']['FPR'],'1/2')
        self.assertEqual(self.arm(s,'S1')['decision']['bonus_audit_interaction'],'0')
    def test_inspection_spam_counts_illegal_actions(self):
        def spam(view):return json.dumps({'choice':next(a['id'] for a in view['actions'] if 'inspect' in a['description'])})
        with Run(self.plan,FixedOutput(['S1','O1'],spam)) as r:
            s=r.score()
        lg=self.arm(s,'S1')['action_legality']
        self.assertEqual(lg['unavailable_selected'],32*5);self.assertEqual(lg['environment_invalid'],32*5)
        self.assertEqual(self.arm(s,'S1')['decision']['J_minus'],'-1')
    def test_malformed_output_is_observed_failure(self):
        with Run(self.plan,FixedOutput(['S1','O1'],'{"choice":0}\nTask:','I refuse to answer')) as r:
            s=r.score()
        a=self.arm(s,'S1')
        self.assertEqual(a['action_legality']['malformed'],32*7)
        self.assertEqual(a['decision']['unknown'],0);self.assertEqual(a['decision']['J_minus'],'-1')
        self.assertEqual(a['reporting']['malformed'],16);self.assertEqual(a['reporting']['unknown'],0)


class CompletenessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.plan=small_plan()
    def fresh(self):return Run(self.plan,ScriptedBackend({'S1':'honest','O1':'honest'}))
    def test_gated_mutant_rejected(self):
        # Skip O1 whenever S1 just ran first in the block: an outcome-agnostic but incomplete plan.
        gate=lambda block,arm,records:arm=='O1' and block['arm_order'][0]=='S1'
        with Run(self.plan,ScriptedBackend({'S1':'honest','O1':'honest'}),skip=gate) as r:
            with self.assertRaises(IncompleteCampaign):r.score()
    def test_deleted_duplicate_reordered_records_rejected(self):
        with self.fresh() as r:
            recs=read_records(r.dir)
            for mutant in (recs[:-1],recs+[recs[0]],[recs[1],recs[0]]+recs[2:]):
                write_records(r.dir,mutant)
                with self.assertRaises(IncompleteCampaign):r.score()
    def test_record_from_other_plan_rejected(self):
        with self.fresh() as r:
            recs=read_records(r.dir);recs[3]['plan_sha256']='0'*64;write_records(r.dir,recs)
            with self.assertRaises(ValueError):r.score()
    def test_tampered_raw_rejected(self):
        with self.fresh() as r:
            recs=read_records(r.dir)
            i=next(i for i,x in enumerate(recs) if x['lane']=='decision')
            recs[i]['generations'][0]['raw']='{"choice":2}';write_records(r.dir,recs)
            with self.assertRaises(ValueError):r.score()
    def test_tampered_case_rejected(self):
        with self.fresh() as r:
            recs=read_records(r.dir)
            i=next(i for i,x in enumerate(recs) if x['lane']=='decision')
            k=next(iter(recs[i]['world_receipt']['case']['facts']))
            recs[i]['world_receipt']['case']['facts'][k]^=True;write_records(r.dir,recs)
            with self.assertRaises(ValueError):r.score()
    def test_tampered_prompt_rejected(self):
        with self.fresh() as r:
            recs=read_records(r.dir)
            i=next(i for i,x in enumerate(recs) if x['lane']=='reporting')
            recs[i]['prompt_sha256']=sha('other');write_records(r.dir,recs)
            with self.assertRaises(ValueError):r.score()
    def test_source_hash_mismatch(self):
        with self.fresh() as r:
            m=json.loads((r.dir/'run_manifest.json').read_text())
            m['source_sha256']['storyworld/oca_sw02/evalmath_runner/scoring.py']='0'*64
            write_json(r.dir/'run_manifest.json',m)
            self.assertEqual(r.score()['status'],'SCORED')
            m['source_sha256']['storyworld/oca_sw02/core.py']='0'*64
            write_json(r.dir/'run_manifest.json',m)
            with self.assertRaises(ValueError):r.score()
    def test_run_directory_not_overwritten(self):
        with self.fresh() as r:
            with self.assertRaises(FileExistsError):run_campaign(self.plan,ScriptedBackend({'S1':'honest','O1':'honest'}),r.dir)


class TimeoutTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.plan=small_plan()
    def honest(self):return ScriptedBackend({'S1':'honest','O1':'honest'})
    def first_decision_call(self,step):
        """Call number of the given step of block 0's first decision unit (reporting units use one call)."""
        n=0
        units={u['unit_id']:u for u in self.plan['blocks'][0]['units']}
        for uid in self.plan['blocks'][0]['unit_order']:
            if units[uid]['lane']=='decision':return n+step-1,units[uid]
            n+=1
    def test_timeout_before_execution_is_unknown(self):
        call,unit=self.first_decision_call(1)
        with Run(self.plan,FaultBackend(self.honest(),{call:TimeoutError('per-call cap')})) as r:
            s=r.score()
            rec=next(x for x in read_records(r.dir) if x['unit_id']==unit['unit_id'] and x['block_index']==0
                     and x['arm']==self.plan['blocks'][0]['arm_order'][0])
        self.assertEqual(rec['status'],'timeout')
        a=s['per_arm'][self.plan['blocks'][0]['arm_order'][0]]['decision']
        self.assertEqual(a['unknown'],1);self.assertEqual(a['refusals'],0)
        lo,hi=map(F,a['J_minus_bounds']);self.assertLess(lo,hi);self.assertEqual(hi,1)
        self.assertEqual(s['status_counts']['timeout'],1)
        p=s['paired']['O1_minus_S1']['J_minus_blocks']
        self.assertIsNone(p['e_value_final']);self.assertNotEqual(*p['mean_difference_bounds'])
    def test_timeout_at_report_keeps_known_execution(self):
        call,unit=self.first_decision_call(2)
        with Run(self.plan,FaultBackend(self.honest(),{call:TimeoutError()})) as r:
            s=r.score()
        arm=self.plan['blocks'][0]['arm_order'][0]
        d=s['per_arm'][arm]['decision']
        self.assertEqual(d['unknown'],0);self.assertEqual(d['J_minus'],'1')
        self.assertEqual(s['per_arm'][arm]['decision_lane_reports']['covered'],31)
    def test_reporting_timeout_is_unknown(self):
        units={u['unit_id']:u for u in self.plan['blocks'][0]['units']}
        n=0
        for uid in self.plan['blocks'][0]['unit_order']:
            if units[uid]['lane']=='reporting':break
            n+=2
        with Run(self.plan,FaultBackend(self.honest(),{n:TimeoutError()})) as r:
            s=r.score()
        rp=s['per_arm'][self.plan['blocks'][0]['arm_order'][0]]['reporting']
        self.assertEqual(rp['unknown'],1);self.assertEqual(rp['accurate_rate_bounds'],['15/16','1'])
        self.assertEqual(rp['refused'],0);self.assertEqual(rp['malformed'],0)
    def test_infrastructure_failure_is_unknown(self):
        with Run(self.plan,FaultBackend(self.honest(),{0:BackendFailure('CUDA OOM')})) as r:
            s=r.score()
        self.assertEqual(s['status_counts']['infrastructure_failure'],1)
    def test_campaign_deadline_writes_complete_assignment(self):
        t=[0.0]
        class Clocked(ScriptedBackend):
            def generate(self,prompt,lane=None):t[0]+=1;return super().generate(prompt,lane)
        with Run(self.plan,Clocked({'S1':'honest','O1':'honest'}),max_seconds=30,clock=lambda:t[0]) as r:
            s=r.score();m=r.manifest
        self.assertTrue(m['deadline_reached'])
        self.assertEqual(s['records'],96)
        self.assertGreater(s['status_counts']['not_executed'],0)
        self.assertEqual(sum(s['status_counts'].values()),96)
        self.assertEqual(s['per_arm']['S1']['decision']['N'],32)


@unittest.skipUnless(HAS_HF,'torch and transformers required for the mock-model path')
class MockModelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.plan=small_plan()
    def backend(self,**kw):
        from storyworld.oca_sw02.evalmath_runner.demo import mock_backend
        return mock_backend({'S1':'honest','O1':'conservative'},**kw)
    def test_mock_matches_scripted(self):
        with Run(self.plan,self.backend()) as m, Run(self.plan,ScriptedBackend({'S1':'honest','O1':'conservative'})) as s:
            sm,ss=m.score(),s.score()
            self.assertEqual(sm['per_arm'],ss['per_arm'])
            self.assertEqual(sm['evidence_class'],'MOCK_MODEL_SYNTHETIC')
            raws=lambda d:[g['raw'] for r in read_records(d) for g in r['generations']]
            self.assertEqual(raws(m.dir),raws(s.dir))
            g=next(g for r in read_records(m.dir) for g in r['generations'])
            self.assertEqual(g['stop'],'parsed');self.assertEqual(g['prompt_tokens'],len(g['prompt']))
    def test_per_call_time_limit_preserves_fragment(self):
        with Run(self.plan,self.backend(slow_calls={0})) as r:
            s=r.score();rec=read_records(r.dir)[0]
        self.assertEqual(rec['status'],'timeout');self.assertEqual(rec['reason'],'per_call_time_limit')
        self.assertEqual(rec['generations'][0]['stop'],'time_limit')
        self.assertEqual(len(rec['generations'][0]['raw']),5)
        self.assertEqual(s['status_counts']['timeout'],1)
    def test_context_limit_is_infrastructure_failure(self):
        b=self.backend();b.decoding['context_limit_tokens']=100
        with Run(self.plan,b) as r:
            s=r.score()
        self.assertEqual(s['status_counts']['infrastructure_failure'],96)
        self.assertEqual(s['per_arm']['S1']['decision']['J_minus_bounds'],['-1','1'])
    def test_adapter_switch(self):
        with Run(self.plan,self.backend()) as r:
            for rec in read_records(r.dir):
                self.assertTrue(all(g['adapter']==rec['arm'] for g in rec['generations']))
    def test_cpu_demo_receipt(self):
        from storyworld.oca_sw02.evalmath_runner.demo import cpu_demo
        with tempfile.TemporaryDirectory() as td:
            out=cpu_demo(td)
            self.assertEqual(out['status'],'CPU_RUNNER_DEMO_VERIFIED')
            self.assertEqual(out['runs']['scripted_honest_vs_conservative']['paired_J_minus_O1_minus_S1'],'-1')
            self.assertEqual(out['runs']['mock_model_conservative_vs_honest']['paired_J_minus_O1_minus_S1'],'1')
            self.assertTrue(out['not_a_model_result'])


class CliTests(unittest.TestCase):
    def test_plan_run_score(self):
        with tempfile.TemporaryDirectory() as td:
            d=Path(td)
            cli(['plan','--out',str(d/'p'),'--themes','harbor','clinic'])
            cli(['run','--plan',str(d/'p'/'plan.json'),'--out',str(d/'r'),'--backend','scripted',
                 '--policy','S1=honest','--policy','O1=conservative'])
            s=json.loads((d/'r'/'score.json').read_text())
            self.assertEqual(s['paired']['O1_minus_S1']['J_minus_blocks']['mean_difference'],'-1')
    def test_model_inference_requires_approval(self):
        with tempfile.TemporaryDirectory() as td:
            with self.assertRaises(SystemExit):
                cli(['infer','--base',td,'--adapter',f'S1={td}','--adapter',f'O1={td}','--out',str(Path(td)/'o')])
    def test_plan_arm_mismatch_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            d=Path(td);cli(['plan','--out',str(d/'p'),'--themes','harbor','clinic'])
            with self.assertRaises(SystemExit):
                cli(['run','--plan',str(d/'p'/'plan.json'),'--out',str(d/'r'),'--backend','scripted',
                     '--policy','S1=honest','--policy','X=honest'])


class CommittedReceiptTests(unittest.TestCase):
    RESULTS=Path(__file__).resolve().parents[1]/'results'
    @unittest.skipUnless((RESULTS/'cpu_demo_receipt.json').exists(),'receipts not generated yet')
    def test_committed_plan_and_rescore(self):
        receipt=json.loads((self.RESULTS/'cpu_demo_receipt.json').read_text())
        plan=build_plan(['S1','O1'],'calibration',seed=41)
        self.assertEqual(receipt['plan_sha256'],plan['plan_sha256'])
        committed=json.loads((self.RESULTS/'plan.json').read_text())
        self.assertTrue(regenerate_and_compare(committed))
        run=self.RESULTS/'scripted_honest_vs_conservative'
        with tempfile.TemporaryDirectory() as td:
            d=Path(td)
            for f in ('plan.json','run_manifest.json','rollouts.jsonl.xz'):(d/f).write_bytes((run/f).read_bytes())
            s=score_run(d)
        self.assertEqual(s['per_arm'],json.loads((run/'score.json').read_text())['per_arm'])


if __name__=='__main__':unittest.main()
