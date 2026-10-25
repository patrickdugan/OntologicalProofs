"""Synthetic fairness/metamorphic test; no inference about actual souls or communities."""
from itertools import product
from experiments.common import emit


def moral_reasons(capable,harm,claim):
    # Chosen toy normative decision: track accountability and repair separately.
    return (bool(capable and harm), bool(harm and claim))


def principled(capable,harm,claim,label):
    return moral_reasons(capable,harm,claim)


def label_sensitive_proxy(capable,harm,claim,label):
    return (bool(capable and harm and label=='X'), bool(harm and label=='X'))


def evaluate():
    scenarios=list(product((False,True),repeat=3))
    principled_label_fail=0
    proxy_label_fail=0
    principled_moral_error=0
    proxy_moral_error=0
    for capacity,harm,claim in scenarios:
        a=principled(capacity,harm,claim,'X')
        b=principled(capacity,harm,claim,'Y')
        x=label_sensitive_proxy(capacity,harm,claim,'X')
        y=label_sensitive_proxy(capacity,harm,claim,'Y')
        principled_label_fail += a!=b
        proxy_label_fail += x!=y
        expected=moral_reasons(capacity,harm,claim)
        principled_moral_error += (a!=expected)+(b!=expected)
        proxy_moral_error += (x!=expected)+(y!=expected)
    assert principled_label_fail==0 and proxy_label_fail>0
    assert principled_moral_error==0 and proxy_moral_error>0
    return dict(synthetic_scenarios=len(scenarios),labels=['X','Y'],
                principled_label_swap_failures=principled_label_fail,
                proxy_label_swap_failures=proxy_label_fail,
                principled_policy_errors=principled_moral_error,
                proxy_policy_errors=proxy_moral_error,
                warning='Whether label is morally irrelevant must be externally specified and reviewed.')

if __name__=='__main__': emit('e05_relevant_invariance.json',evaluate())
