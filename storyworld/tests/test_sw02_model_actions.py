"""CPU-only regression tests for the model-facing action affordance contract."""
import copy
import json
import unittest
from storyworld.oca_sw02.core import World,make_case,available_choice,rollout,replay
from storyworld.oca_sw02.evaluate import action_prompt,model_observation,parse_action

class ModelAffordances(unittest.TestCase):
    def case(self):return make_case('harbor',6,1,'calibration')

    def test_exhausted_inspection_is_visibly_unavailable(self):
        w=World(self.case())
        inspect=available_choice(w.observation(),'inspect')
        before=copy.deepcopy(w.observation())
        self.assertTrue(next(a for a in model_observation(before)['actions'] if a['id']==inspect)['available'])
        for _ in range(2):w.step({'choice':inspect})
        ob=w.observation()
        marked=model_observation(ob)
        option=next(a for a in marked['actions'] if a['id']==inspect)
        self.assertFalse(option['available'])
        self.assertIn('No inspection slots',option['availability_note'])
        self.assertFalse(any('available' in a for a in ob['actions']))
        self.assertEqual(w.state.invalid,0)
        w.step({'choice':inspect})
        self.assertEqual(w.state.invalid,1)

    def test_redundant_second_inspection_is_not_hidden(self):
        w=World(self.case())
        inspect=available_choice(w.observation(),'inspect')
        w.step({'choice':inspect})
        item=next(a for a in model_observation(w.observation())['actions'] if a['id']==inspect)
        self.assertTrue(item['available'])
        self.assertIn('no new authenticated facts',item['availability_note'])

    def test_second_repair_is_visibly_unavailable(self):
        w=World(self.case())
        w.step({'choice':available_choice(w.observation(),'execute')})
        self.assertTrue(model_observation(w.observation())['actions'][2]['available'])
        w.step({'choice':2})
        actions=model_observation(w.observation())['actions']
        self.assertFalse(actions[2]['available'])
        self.assertTrue(actions[0]['available'])
        self.assertTrue(actions[1]['available'])

    def test_model_prompt_and_world_observation_separation(self):
        w=World(self.case())
        public=w.observation()
        serial=action_prompt(public)
        encoded=json.loads(serial.split('Observation:\n',1)[1].split('\nAction JSON:',1)[0])
        self.assertEqual([a['id'] for a in public['actions']],[a['id'] for a in encoded['actions']])
        self.assertTrue(all(a['available'] for a in encoded['actions']))
        for forbidden in ('allowed','facts','hidden','family','history_id'):
            self.assertNotIn(forbidden, encoded)
        self.assertNotIn('available',public['actions'][0])
        self.assertEqual(parse_action('{"choice":1}'),{'choice':1})

    def test_archived_receipts_still_replay(self):
        receipt,_=rollout(self.case(),'honest')
        self.assertTrue(replay(json.loads(json.dumps(receipt))))

if __name__=='__main__':unittest.main()
