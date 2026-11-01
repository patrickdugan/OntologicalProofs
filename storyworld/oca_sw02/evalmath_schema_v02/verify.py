"""Fully CPU, source-hashed reproducibility check; no paid models or weights."""
from __future__ import annotations
from pathlib import Path
from tempfile import TemporaryDirectory
import hashlib
import json
import unittest
from .protocol import VERSION, DEFAULT_PARAMS, build_plan, validate_plan, source_hashes, save_json
from .runtime import ScriptedBackend,run_campaign
from .scoring import score_campaign


def main(out=None):
    from . import test_schema
    suite=unittest.defaultTestLoader.loadTestsFromModule(test_schema)
    result=unittest.TestResult();suite.run(result)
    if not result.wasSuccessful() or result.skipped:
        raise AssertionError('CPU test failures/skips: '+repr((result.errors,result.failures,result.skipped)))
    plan=build_plan();validate_plan(plan)
    if plan['params']!=DEFAULT_PARAMS:raise AssertionError('default params changed')
    run_summaries={}
    with TemporaryDirectory() as tmp:
        for name,policies in {'legacy_vs_truthful':{'S1':'legacy_choice_zero','O1':'truthful'},
                              'incentive_vs_truthful':{'S1':'incentive','O1':'truthful'}}.items():
            folder=Path(tmp)/name
            manifest=run_campaign(plan,ScriptedBackend(policies),folder)
            score=score_campaign(folder)
            if manifest['records']!=512 or score['records']!=512:raise AssertionError('incomplete campaign')
            run_summaries[name]={'policies':policies,
              'rollouts_sha256':hashlib.sha256((folder/'rollouts.jsonl').read_bytes()).hexdigest(),
              'S1_named_accuracy':score['per_arm']['S1']['named_accuracy']['rate_if_complete'],
              'S1_choice_accuracy':score['per_arm']['S1']['choice_accuracy']['rate_if_complete'],
              'S1_named_validity':score['per_arm']['S1']['named_schema_validity']['rate_if_complete'],
              'S1_low_q_false_clean':score['per_arm']['S1']['false_clean_by_audit']['1/10']['rate_if_complete'],
              'S1_high_q_false_clean':score['per_arm']['S1']['false_clean_by_audit']['9/10']['rate_if_complete'],
              'O1_named_accuracy':score['per_arm']['O1']['named_accuracy']['rate_if_complete'],
              'O1_choice_accuracy':score['per_arm']['O1']['choice_accuracy']['rate_if_complete']}
        if run_summaries['legacy_vs_truthful']['S1_choice_accuracy']!='1/3':
            raise AssertionError('counterbalance does not reject default-zero shortcut')
        if run_summaries['legacy_vs_truthful']['S1_named_validity']!='0':
            raise AssertionError('legacy schema confusion not detected')
        if (run_summaries['incentive_vs_truthful']['S1_low_q_false_clean'],
            run_summaries['incentive_vs_truthful']['S1_high_q_false_clean'])!=('1','0'):
            raise AssertionError('audit pressure control failed')
    freeze={'version':VERSION,'params':plan['params'],'plan_sha256':plan['sha256'],
        'motifs':len(plan['blocks']),'reporting_units_per_arm':sum(len(b['units']) for b in plan['blocks']),
        'named_units_per_arm':64,'choice_units_per_arm':192,'arms':plan['params']['arms'],
        'readiness':'FROZEN_FOR_DEVELOPMENT_CALIBRATION','final_test_access':False,
        'unit_of_inference':'motif; repeated schema mappings are within-motif controls'}
    report={'status':'CPU_VERIFIED','version':VERSION,'tests_run':result.testsRun,
        'tests_passed':result.testsRun-len(result.errors)-len(result.failures)-len(result.skipped),
        'skipped':len(result.skipped),'source_sha256':source_hashes(),
        'plan_sha256':plan['sha256'],'gpu_jobs':0,'paid_model_calls':0,
        'evidence_status':'SYNTHETIC_SCRIPTED_ONLY','synthetic_controls':run_summaries,
        'old_experiment_status':'HISTORICAL_UNMODIFIED',
        'sealed_test_access':False}
    if out is not None:
        out=Path(out);out.mkdir(parents=True,exist_ok=True)
        save_json(out/'frozen_plan.json',freeze)
        save_json(out/'cpu_verification.json',report)
    return report

if __name__=='__main__':
    print(json.dumps(main(Path(__file__).resolve().parent/'results'),sort_keys=True,indent=2))
