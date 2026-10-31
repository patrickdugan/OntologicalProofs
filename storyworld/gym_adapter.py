"""Optional real Gymnasium adapter; the core stays dependency-free."""
from __future__ import annotations
import json
import string
import gymnasium as gym
from gymnasium import spaces
from .oca import THEMES, World, make_case

class OntologicalStoryworldEnv(gym.Env):
    metadata={'render_modes':['ansi']}
    def __init__(self, render_mode=None, gate=False, horizon=8):
        if render_mode not in (None,'ansi'): raise ValueError('render_mode')
        self.render_mode,self.gate,self.horizon=render_mode,gate,horizon
        self.action_space=spaces.Discrete(4)
        self.observation_space=spaces.Text(max_length=24000,min_length=1,charset=string.printable)
        self.world=None
    def reset(self, *, seed=None, options=None):
        super().reset(seed=seed)
        options=options or {}
        theme=options.get('theme',list(THEMES)[int(self.np_random.integers(len(THEMES)))])
        mechanism=int(options.get('mechanism',self.np_random.integers(3)))
        instance=int(options.get('instance',self.np_random.integers(16)))
        case=make_case(theme,mechanism,instance,'dev',int(self.np_random.integers(2**31)))
        case=case.variant(bool(options.get('oversight',False)),bool(options.get('bonus',False)))
        self.world=World(case,self.gate,self.horizon)
        return json.dumps(self.world.observation(),sort_keys=True,ensure_ascii=True),{}
    def step(self, action):
        if self.world is None: raise RuntimeError('reset first')
        raw={'stop':True} if int(action)==3 and self.action_space.contains(action) else {'choice':int(action)}
        obs,reward,terminated,truncated,info=self.world.step(raw)
        return json.dumps(obs,sort_keys=True,ensure_ascii=True),reward,terminated,truncated,info
    def render(self):
        return None if self.world is None else json.dumps(self.world.observation(),indent=2)
    def evaluator_receipt(self):
        """Host-side scorer API. Exclude this method from learner tools."""
        if self.world is None: raise RuntimeError('reset first')
        return self.world.receipt()

gym.register('OntologicalStoryworld-v0',entry_point='storyworld.gym_adapter:OntologicalStoryworldEnv')
