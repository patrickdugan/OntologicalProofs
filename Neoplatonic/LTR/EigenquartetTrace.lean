import Neoplatonic.LTR.OrthogonalTraceDecomposition
import Neoplatonic.LTR.TwoDirectionQuartetExistence
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Tactic

/-!
# LTR-MAN-63: trace of an invariant orthonormal eigenquartet

MAN-62 splits the ambient trace across a submodule K and Kᗮ.
The signed Hamming coordinate operators act diagonally on the
orthonormal quartet from MAN-58, with eigenvalues 1,-1,0,0 or
0,0,1,-1.

We prove an abstract lemma identifying the trace of a restriction to
the span of any finite orthonormal eigenfamily with the sum of its
eigenvalues. Combined with MAN-62 and ambient trace zero, this
forces the trace of the invariant residual compression to vanish.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- An operator diagonal on an orthonormal quartet preserves
the linear span of that quartet. -/
theorem eigenquartet_span_invariant
    (q : Fin 4 → E) (T : E →ₗ[ℂ] E)
    (λ : Fin 4 → ℂ)
    (hEig : ∀ i : Fin 4, T (q i) = λ i • q i) :
    ∀ x ∈ Submodule.span ℂ (Set.range q),
      T x ∈ Submodule.span ℂ (Set.range q) := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [hEig i]
      exact (Submodule.span ℂ (Set.range q)).smul_mem
        (λ i) (Submodule.subset_span (Set.mem_range_self i))
  | zero =>
      simp
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using
        (Submodule.span ℂ (Set.range q)).add_mem ihx ihy
  | smul a x hx ihx =>
      simpa only [map_smul] using
        (Submodule.span ℂ (Set.range q)).smul_mem a ihx

/-- In an orthonormal eigenquartet basis, the trace of the
restriction to its span equals the sum of the four eigenvalues. -/
theorem eigenquartet_span_restrict_trace
    (q : Fin 4 → E) (hq : Orthonormal ℂ q)
    (T : E →ₗ[ℂ] E) (λ : Fin 4 → ℂ)
    (hEig : ∀ i : Fin 4, T (q i) = λ i • q i)
    (hK : ∀ x ∈ Submodule.span ℂ (Set.range q),
      T x ∈ Submodule.span ℂ (Set.range q)) :
    LinearMap.trace ℂ (Submodule.span ℂ (Set.range q))
        (T.restrict hK) = ∑ i : Fin 4, λ i := by
  classical
  let K := Submodule.span ℂ (Set.range q)
  let b0 : Basis (Fin 4) ℂ K := Basis.span hq.linearIndependent
  have horth : Orthonormal ℂ (b0 : Fin 4 → K) := by
    simpa only [b0, Basis.span_apply] using (orthonormal_span hq)
  let b : OrthonormalBasis (Fin 4) ℂ K :=
    OrthonormalBasis.mk horth b0.span_eq.ge
  have hb (i : Fin 4) : ((b i : K) : E) = q i := by
    simp [b, b0, OrthonormalBasis.coe_mk, Basis.span_apply]
  have heigB (i : Fin 4) :
      (T.restrict hK) (b i) = λ i • b i := by
    apply Subtype.ext
    change T (b i : E) = λ i • (b i : E)
    rw [hb i]
    exact hEig i
  calc
    LinearMap.trace ℂ K (T.restrict hK) =
        ∑ i : Fin 4, inner ℂ (b i) ((T.restrict hK) (b i)) :=
      LinearMap.trace_eq_sum_inner (T.restrict hK) b
    _ = ∑ i : Fin 4, λ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [heigB i, inner_smul_right]
      have hinner : inner ℂ (b i) (b i) = 1 := by
        simpa only [if_pos rfl] using
          (orthonormal_iff_ite.mp b.orthonormal) i i
      simp [hinner]

/-- For an ambient trace-zero operator, the residual trace is
zero whenever the four orthonormal eigenvalues sum to zero. -/
theorem eigenquartet_residual_restrict_trace_zero
    (q : Fin 4 → E) (hq : Orthonormal ℂ q)
    (T : E →ₗ[ℂ] E) (λ : Fin 4 → ℂ)
    (hEig : ∀ i : Fin 4, T (q i) = λ i • q i)
    (htr : LinearMap.trace ℂ E T = 0)
    (hsum : (∑ i : Fin 4, λ i) = 0)
    (hR : ∀ x ∈ (Submodule.span ℂ (Set.range q))ᗮ,
      T x ∈ (Submodule.span ℂ (Set.range q))ᗮ) :
    LinearMap.trace ℂ ((Submodule.span ℂ (Set.range q))ᗮ)
      (T.restrict hR) = 0 := by
  have hK := eigenquartet_span_invariant q T λ hEig
  have hsplit := orthogonalTwoSummands_trace
    (Submodule.span ℂ (Set.range q)) T hK hR
  have hquartet :=
    eigenquartet_span_restrict_trace q hq T λ hEig hK
  rw [htr, hquartet, hsum] at hsplit
  simpa using hsplit.symm

end Neoplatonic.LTR
