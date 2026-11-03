import Neoplatonic.LTR.ComplexObservableFaithful
import Mathlib.Topology.Closure

/-!
# Faithfulness of a dense marked complex Hilbert representation

If a continuous real function vanishes on a dense sequence, it
vanishes on the whole space. Combine this with the kernel-verified
single-block faithfulness of the bounded complex representation:
when every dense sample appears as a marked endpoint, a represented
continuous observable vanishes on H only if the function vanishes
at every point of the completion space.

This is a concrete point-separation/faithfulness theorem for the
real-valued observable algebra, without yet bundling an abstract
complex C(X)-algebra homomorphism.
-/

namespace Neoplatonic.LTR

/-- A continuous real function vanishing at every point in a dense
countable sequence vanishes everywhere. -/
theorem continuous_real_eq_zero_of_dense_sequence
    {X : Type*} [TopologicalSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (a : X → ℝ) (ha : Continuous a)
    (hzero : ∀ n, a (q n) = 0) :
    ∀ x : X, a x = 0 := by
  let S : Set X := {x | a x = 0}
  have hclosed : IsClosed S := isClosed_eq ha continuous_const
  have hsub : Set.range q ⊆ S := by
    rintro x ⟨n, rfl⟩
    exact hzero n
  have hfull : Set.univ ⊆ S := by
    simpa only [hq.closure_eq] using closure_minimal hsub hclosed
  intro x
  exact hfull (Set.mem_univ x)

/-- For a dense countable marking with every dense sample occurring
at an endpoint, the complex Hilbert representation of a bounded
continuous real observable is faithful. -/
theorem complexDenseObservable_faithful
    {X : Type*} [TopologicalSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hcover : ∀ n, ∃ j, left j = q n ∨ right j = q n)
    (a : X → ℝ) (ha : Continuous a)
    (M : ℝ) (hM : 0 ≤ M)
    (hBound : ∀ j,
       |a (left j)| ≤ M ∧ |a (right j)| ≤ M)
    (hzero : complexPairObservableCLM
      (fun j => a (left j)) (fun j => a (right j))
      M hM hBound = 0) :
    ∀ x : X, a x = 0 := by
  have hend := complexPairObservableCLM_eq_zero_values
    (fun j => a (left j)) (fun j => a (right j))
    M hM hBound hzero
  apply continuous_real_eq_zero_of_dense_sequence q hq a ha
  intro n
  obtain ⟨j, hl | hr⟩ := hcover n
  · simpa [hl] using (hend j).1
  · simpa [hr] using (hend j).2

end Neoplatonic.LTR
