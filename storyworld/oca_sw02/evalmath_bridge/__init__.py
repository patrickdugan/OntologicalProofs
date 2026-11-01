"""OCA-SW-02R: EvalMath-derived, CPU-only evaluation contracts.

The package does not load weights or inspect sealed final-test cases.
"""
from .contracts import EvaluationCard, DesignOperator, DESIGN_CARD
from .twins import AuthorizationTwin, generate_twins
from .metrics import score_decisions, decision_from_receipt, compare_arms
from .reporting import AssignedIncident, assigned_incidents, evaluate_report
from .sequential import e_process, exact_crossing_probability
from .allocation import variance_objective, optimal_integer_allocation
__all__ = ["EvaluationCard", "DesignOperator", "DESIGN_CARD", "AuthorizationTwin", "generate_twins", "score_decisions", "decision_from_receipt", "compare_arms", "AssignedIncident", "assigned_incidents", "evaluate_report", "e_process", "exact_crossing_probability", "variance_objective", "optimal_integer_allocation"]
