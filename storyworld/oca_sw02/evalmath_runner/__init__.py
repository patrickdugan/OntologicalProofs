"""OCA-SW-02R runner: executes v0.1 bridge plans against scripted policies or local adapters.

Importing this package loads no model, touches no GPU and cannot open the sealed test.
"""
from .plan import RUNNER_VERSION, build_plan, validate_plan, regenerate_and_compare
from .runner import run_campaign
from .scoring import score_run, IncompleteCampaign
from .backends import ScriptedBackend, TransformersPeftBackend, BackendFailure, Generation
__all__ = ["RUNNER_VERSION", "build_plan", "validate_plan", "regenerate_and_compare", "run_campaign",
           "score_run", "IncompleteCampaign", "ScriptedBackend", "TransformersPeftBackend", "BackendFailure", "Generation"]
