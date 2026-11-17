"""Exact finite audits. These are synthetic logical checks, with no model calls."""
from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from itertools import product
import json


def posterior(prior: Fraction, hit: Fraction, false_alarm: Fraction) -> Fraction:
    """Binary Bayes update; likelihoods must describe the sampled evidence event."""
    for value in (prior, hit, false_alarm):
        if not isinstance(value, Fraction):
            raise TypeError("Use exact Fraction inputs")
        if not 0 <= value <= 1:
            raise ValueError("Probabilities must lie in [0, 1]")
    evidence = prior * hit + (1 - prior) * false_alarm
    if evidence == 0:
        raise ValueError("Conditioning event has zero probability")
    return prior * hit / evidence


def decode_possible(view: tuple[int, ...], duty: tuple[int, ...]) -> bool:
    if len(view) != len(duty) or not view:
        raise ValueError("Equal, nonempty domains are required")
    if any(v not in (0, 1) for v in view + duty):
        raise ValueError("This audit uses binary views and duties")
    return any(all(decoder[v] == d for v, d in zip(view, duty))
               for decoder in product(range(2), repeat=2))


def fiber_consistent(view: tuple[int, ...], duty: tuple[int, ...]) -> bool:
    return all(view[x] != view[y] or duty[x] == duty[y]
               for x in range(len(view)) for y in range(len(view)))


def edges_from_mask(mask: int) -> tuple[tuple[int, int, int], ...]:
    if type(mask) is not int or not 0 <= mask < 256:
        raise ValueError("An edge mask is an integer in [0, 255]")
    return tuple((s, a, t) for s, a, t in product(range(2), repeat=3)
                 if mask & (1 << ((s * 2 + a) * 2 + t)))


def reachable_states(initial: int, edges: tuple[tuple[int, int, int], ...]) -> int:
    reached = initial
    while True:
        expanded = reached
        for source, _, target in edges:
            if reached & (1 << source):
                expanded |= 1 << target
        if expanded == reached:
            return reached
        reached = expanded


def contract_flags(initial: int, invariant: int, edges: tuple[tuple[int, int, int], ...],
                   gate: int, lawful: int) -> dict[str, bool]:
    invariant_pairs = sum(3 << (2 * s) for s in range(2) if invariant & (1 << s))
    executed_pairs = 0
    for s, a, _ in edges:
        executed_pairs |= 1 << (2 * s + a)
    return {
        "starts": initial & ~invariant == 0,
        "preserves": all(not invariant & (1 << s) or invariant & (1 << t)
                         for s, _, t in edges),
        "mediation": executed_pairs & ~gate == 0,
        "sound": invariant_pairs & gate & ~lawful == 0,
    }


def unsafe_reachable_effect(initial: int, edges: tuple[tuple[int, int, int], ...],
                            lawful: int) -> bool:
    reached = reachable_states(initial, edges)
    return any(reached & (1 << s) and not lawful & (1 << (2 * s + a))
               for s, a, _ in edges)


@lru_cache(maxsize=1)
def audit_execution() -> dict:
    """Enumerate every two-state/two-action system in the declared encoding."""
    counts = {"systems": 0, "contracts": 0, "contracts_with_initial_state": 0,
              "contracts_with_reachable_effect": 0, "unsafe_contracts": 0}
    witnesses: dict[str, dict] = {}
    keys = ("starts", "preserves", "mediation", "sound")
    # Predicates are bitsets. Every transition relation has eight possible edges.
    for edge_mask in range(256):
        edges = edges_from_mask(edge_mask)
        executed_pairs = 0
        for s, a, _ in edges:
            executed_pairs |= 1 << (2 * s + a)
        for initial in range(4):
            reached = reachable_states(initial, edges)
            reachable_pairs = 0
            for s, a, _ in edges:
                if reached & (1 << s):
                    reachable_pairs |= 1 << (2 * s + a)
            for invariant in range(4):
                starts = initial & ~invariant == 0
                preserves = all(not invariant & (1 << s) or invariant & (1 << t)
                                for s, _, t in edges)
                inv_pairs = sum(3 << (2 * s) for s in range(2) if invariant & (1 << s))
                for gate in range(16):
                    mediation = executed_pairs & ~gate == 0
                    for lawful in range(16):
                        sound = inv_pairs & gate & ~lawful == 0
                        flags = (starts, bool(preserves), mediation, sound)
                        unsafe = reachable_pairs & ~lawful != 0
                        counts["systems"] += 1
                        if all(flags):
                            counts["contracts"] += 1
                            counts["contracts_with_initial_state"] += bool(initial)
                            counts["contracts_with_reachable_effect"] += bool(reachable_pairs)
                            counts["unsafe_contracts"] += unsafe
                        if unsafe and sum(flags) == 3:
                            missing = keys[flags.index(False)]
                            if missing not in witnesses:
                                witnesses[missing] = {
                                    "initial": initial, "invariant": invariant,
                                    "edge_mask": edge_mask, "edges": [list(e) for e in edges],
                                    "gate": gate, "lawful": lawful,
                                    "holds": dict(zip(keys, flags)),
                                }
    if counts["unsafe_contracts"] or set(witnesses) != set(keys):
        raise AssertionError("Execution implication or premise-deletion audit failed")
    return {**counts, "premise_deletion_witnesses": witnesses}


def audit_information() -> dict:
    total = obstructed = 0
    for view in product(range(2), repeat=4):
        for duty in product(range(2), repeat=4):
            possible = decode_possible(view, duty)
            if possible != fiber_consistent(view, duty):
                raise AssertionError("Fiber factorization mismatch")
            total += 1
            obstructed += not possible
    return {"view_duty_pairs": total, "obstructed": obstructed}


def audit_guidance() -> dict:
    total = increase = equal = decrease = zero_event = 0
    for p in range(1, 10):
        prior = Fraction(p, 10)
        for h, f in product(range(11), repeat=2):
            hit, false_alarm = Fraction(h, 10), Fraction(f, 10)
            if h == f == 0:
                zero_event += 1
                continue
            updated = posterior(prior, hit, false_alarm)
            if (updated > prior) != (hit > false_alarm):
                raise AssertionError("Likelihood comparison failed")
            total += 1
            increase += updated > prior
            equal += updated == prior
            decrease += updated < prior
    return {"positive_event_cases": total, "increases": increase, "unchanged": equal,
            "decreases": decrease, "zero_probability_events_excluded": zero_event}


def audit_motivation() -> dict:
    cases = qualifying = 0
    for lawful in range(16):
        for scores in product(range(3), repeat=4):
            feasible = lawful != 0
            priority = all(scores[bad] < scores[good]
                           for good, bad in product(range(4), repeat=2)
                           if lawful & (1 << good) and not lawful & (1 << bad))
            for chosen in range(4):
                cases += 1
                maximizes = all(score <= scores[chosen] for score in scores)
                if feasible and priority and maximizes:
                    qualifying += 1
                    if not lawful & (1 << chosen):
                        raise AssertionError("Strict moral priority implication failed")
    return {"candidate_cases": cases, "qualifying_maximizers": qualifying}


def audit_all() -> dict:
    return {"schema": "moral_realism_finite_audit_v1", "domain": "synthetic_only",
            "execution": audit_execution(), "information": audit_information(),
            "guidance": audit_guidance(), "motivation": audit_motivation()}


if __name__ == "__main__":
    print(json.dumps(audit_all(), indent=2, sort_keys=True))
