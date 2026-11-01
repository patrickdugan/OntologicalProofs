"""Optional Gymnasium adapter for the independently scored OCA-SW-02 world."""
from __future__ import annotations
import json
import string
import gymnasium as gym
from gymnasium import spaces
from .core import SCENES,SPLITS,World,make_case

class AdversarialStoryworldEnv(gym.Env):
    metadata={'render_modes':['ansi']}
    def __init__(self,render_mode=None,horizon=7,gate=False):
        if render_mode not in (None,'ansi'):raise ValueError('unsupported render mode')
        self.render_mode,self.horizon,self.gate=render_mode,horizon,gate
        self.action_space=spaces.Discrete(4)
        self.observation_space=spaces.Text(max_length=24000,min_length=1,charset=string.printable)
        self.world=None
    def reset(self,*,seed=None,options=None):
        super().reset(seed=seed)
        options=options or {}
        split=options.get('split','development')
        if split not in ('development','calibration'):raise ValueError('sealed test unavailable in Gym API')
        fams=(0,1) if split=='development' else SPLITS['calibration']
        family=int(options.get('family',fams[int(self.np_random.integers(len(fams)))]))
        if family not in fams:raise ValueError('family outside public split')
        theme=options.get('theme',list(SCENES)[int(self.np_random.integers(len(SCENES)))])
        instance=int(options.get('instance',self.np_random.integers(16)))
        case=make_case(theme,family,instance,split=split,seed=int(options.get('case_seed',self.np_random.integers(2**31))))
        self.world=World(case.variant(bool(options.get('watched',False)),bool(options.get('bonus',False))),self.gate,self.horizon)
        return json.dumps(self.world.observation(),sort_keys=True,ensure_ascii=True),{}
    def step(self,action):
        if self.world is None:raise RuntimeError('reset first')
        if not self.action_space.contains(action):raw='INVALID_ACTION'
        else:raw={'stop':True} if int(action)==3 else {'choice':int(action)}
        ob,reward,done,truncated,info=self.world.step(raw)
        return json.dumps(ob,sort_keys=True,ensure_ascii=True),float(reward),bool(done),bool(truncated),info
    def render(self):
        return None if self.world is None else json.dumps(self.world.observation(),indent=2)
    def evaluator_receipt(self):
        """Host-only interface; never expose to an untrusted model process."""
        if self.world is None:raise RuntimeError('reset first')
        return self.world.receipt()

gym.register('OCA-AdversarialStoryworld-v0',entry_point='storyworld.oca_sw02.env:AdversarialStoryworldEnv')
