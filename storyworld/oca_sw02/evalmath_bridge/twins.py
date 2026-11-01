"""Authorization twins with one pivotal authenticated fact and matched exogenous keys."""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from random import Random
from dataclasses import replace
from .contracts import DESIGN_CARD
from ..core import Case, RULES, SCENES, SPLITS, eval_ast, oracle_dnf, variables, digest, World

@dataclass(frozen=True)
class AuthorizationTwin:
    motif_id: str
    theme: str
    family: int
    pivot: str
    unauthorized: Case
    authorized: Case

    def variants(self):
        for authorized,case in ((False,self.unauthorized),(True,self.authorized)):
            for watched,bonus in product((False,True),repeat=2):
                yield {'motif_id':self.motif_id, 'authorized':authorized,
                       'watched':watched, 'bonus':bonus,
                       'case':case.variant(watched,bonus),
                       'audit_key':digest([self.motif_id,'audit',int(watched),int(bonus)]),
                       'permutation_key':digest([self.motif_id,'action-order'])}

    def verify(self):
        a,b=self.unauthorized,self.authorized
        if a.allowed or not b.allowed:raise AssertionError('authorization twin direction wrong')
        if (a.theme,a.family,a.choice_order,a.hidden)!=(b.theme,b.family,b.choice_order,b.hidden):
            raise AssertionError('unmatched public context or action order')
        changed=[k for k in a.facts if a.facts[k]!=b.facts[k]]
        if changed!=[self.pivot]:raise AssertionError('twin must vary one pivotal fact')
        if not oracle_dnf(a.family,a.facts)==a.allowed or not oracle_dnf(b.family,b.facts)==b.allowed:
            raise AssertionError('AST/DNF mismatch')
        left=World(a).observation();right=World(b).observation()
        for k in ('title','brief','charter','written_rule','actions','inspection_slots'):
            if left[k]!=right[k]:raise AssertionError('unmatched public field: '+k)
        # Source labels and chronology remain equal (instances 2k and 2k+1).
        if left['untrusted_statement']!=right['untrusted_statement']:
            raise AssertionError('changed untrusted testimony')
        for obj in self.variants():
            c=obj['case']
            if c.allowed!=obj['authorized']:raise AssertionError('cue changed authorization')
            if len(World(c).observation()['actions'])!=3:raise AssertionError('lost physical action')
        return True


def generate_twins(split='train',families=None,themes=None,motifs_per_family=1,seed=41):
    """Use train families by default; final-test generation is refused.

    Each motif is a deterministic random draw from the complete finite pivotal-pair
    set, rather than chosen by an S1/O1 model score.
    """
    if split not in ('train','calibration'):raise ValueError('sealed test forbidden')
    fams=tuple(SPLITS[split]) if families is None else tuple(families)
    if any(f not in SPLITS[split] for f in fams):raise ValueError('family outside split')
    if motifs_per_family<1:raise ValueError('empty motif budget')
    selected=tuple(SCENES) if themes is None else tuple(themes)
    if any(t not in SCENES for t in selected):raise ValueError('unknown scene')
    for family in fams:
        ast=RULES[family][0]
        keys=sorted(variables(ast))
        pairs=[]
        for bits in product((False,True),repeat=len(keys)):
            facts=dict(zip(keys,bits))
            if eval_ast(ast,facts):continue
            for pivot in keys:
                other={**facts,pivot:not facts[pivot]}
                if eval_ast(ast,other):
                    if not oracle_dnf(family,facts) and oracle_dnf(family,other):
                        pairs.append((facts,pivot,other))
        if not pairs:raise ValueError('family lacks pivotal true/false twins')
        for theme in selected:
            rng=Random(int(digest(['twin-selection',seed,theme,family]),16))
            for k in range(motifs_per_family):
                false_f,pivot,true_f=pairs[rng.randrange(len(pairs))]
                order=['change','retain','inspect'];rng.shuffle(order)
                motif=digest(['OCA-SW02R',seed,theme,family,k,pivot,false_f])[:24]
                kwargs=dict(theme=theme,family=family,split=split,hidden=None,choice_order=tuple(order))
                low=Case(instance=2*k, facts=false_f.copy(),history_id=digest([motif,0])[:20],**kwargs)
                high=Case(instance=2*k+1, facts=true_f.copy(),history_id=digest([motif,1])[:20],**kwargs)
                twin=AuthorizationTwin(motif,theme,family,pivot,low,high)
                twin.verify()
                yield twin
