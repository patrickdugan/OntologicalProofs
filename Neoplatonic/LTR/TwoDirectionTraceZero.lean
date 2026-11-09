import Neoplatonic.LTR.IdempotentGradingPairing
import Mathlib.LinearAlgebra.Trace

/-!
# LTR-MAN-15A: zero trace of finite-dimensional coordinate commutators

The next stage of the two-bit Hamming lower bound uses the fact that
the two Hermitian coordinate commutators have trace zero. The
matrix-independent proof is the cyclic property of the trace.

For any complex linear maps D and P, including a self-adjoint
Dirac operator and a projection onto one Boolean truth coordinate,

  trace(DP - PD) = 0.

Multiplying the commutator by the complex imaginary unit also
preserves zero trace. Hence the Hermitian observable
A = i[D,P] is traceless, as required by the residual-space argument.

No idempotence or Hilbert structure is needed for the trace identity.
The trace of a linear map is defined using any finite module basis;
it agrees with matrix trace in finite dimension.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Cyclicity of trace makes any finite-dimensional complex
endomorphism commutator traceless. -/
theorem complexEndomorphism_commutator_trace_zero
    (D P : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ E (D * P - P * D) = 0 := by
  rw [map_sub, LinearMap.trace_mul_comm ℂ D P, sub_self]

/-- The Hermitian coordinate commutator i[D,P] is traceless. -/
theorem imaginary_commutator_trace_zero
    (D P : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ E (Complex.I • (D * P - P * D)) = 0 := by
  rw [map_smul, complexEndomorphism_commutator_trace_zero, smul_zero]

end Neoplatonic.LTR
