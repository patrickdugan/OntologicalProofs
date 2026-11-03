import Neoplatonic.LTR.Stone
import Neoplatonic.LTR.Network

/-!
# Conservative reconstruction

The same sentence labels are retained on the local completion space and on
the global realization. Surjectivity of the projection means every local
completion extends. Under that condition, global gluing preserves the exact
coverage predicate, including its computability status.
-/

namespace Neoplatonic.LTR

open FirstOrder Set

universe u v w z

variable {L : FirstOrder.Language.{u, v}} {T : L.Theory} {α : Type w}

/-- Independent local sentences stay independent after a surjective realization. -/
theorem independence_survives_realization
    {X : Type z} (f : X → T.CompleteType α)
    (hf : Function.Surjective f) (φ : (L.withConstants α).Sentence) :
    Independent T φ ↔
      (f ⁻¹' T.typesWith φ).Nonempty ∧
      f ⁻¹' T.typesWith φ ≠ Set.univ := by
  rw [independent_iff_nontrivial_locus]
  simp only [Set.nonempty_iff_ne_empty, ne_eq,
    empty_pullback_iff f hf, cover_pullback_iff f hf]

/-- A continuous realization also preserves the clopen structure. -/
theorem realized_locus_isClopen
    {X : Type z} [TopologicalSpace X]
    (f : X → T.CompleteType α) (hf : Continuous f)
    (φ : (L.withConstants α).Sentence) :
    IsClopen (f ⁻¹' T.typesWith φ) :=
  (locus_isClopen φ).preimage hf

/-- Exact effective preservation in the common sentence-code presentation. -/
theorem realized_cover_computable_iff
    {X : Type z} (f : X → T.CompleteType α)
    (hf : Function.Surjective f)
    (code : ℕ → (L.withConstants α).Sentence) :
    ComputablePred (fun n => f ⁻¹' T.typesWith (code n) = Set.univ) ↔
    ComputablePred (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n) := by
  have heq : (fun n => f ⁻¹' T.typesWith (code n) = Set.univ) =
      (fun n => T.typesWith (code n) = Set.univ) := by
    funext n
    exact propext (cover_pullback_iff f hf _)
  rw [heq]
  exact cover_computable_iff code

/-- The global geometric cover problem inherits local logical undecidability.
No computation of a completion point, nor of the realization map, is required:
the finite input remains the same sentence code. -/
theorem realized_cover_noncomputable
    {X : Type z} (f : X → T.CompleteType α)
    (hf : Function.Surjective f)
    (code : ℕ → (L.withConstants α).Sentence)
    (h : ¬ ComputablePred
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n)) :
    ¬ ComputablePred
      (fun n => f ⁻¹' T.typesWith (code n) = Set.univ) := by
  intro hc
  exact h ((realized_cover_computable_iff f hf code).mp hc)

/-- The full finite-extension-to-independence theorem. The ambient compact
space may be a product of local completion spaces. The family C includes all
interface equations, and f selects the distinguished local component. -/
theorem finite_extension_preserves_independence
    {X : Type z} {K : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (C : K → Set X) (hclosed : ∀ k, IsClosed (C k))
    (f : X → T.CompleteType α) (hf : Continuous f)
    (hfinite : ∀ y : T.CompleteType α, ∀ s : Finset K,
      ∃ x : X, f x = y ∧ ∀ k ∈ s, x ∈ C k)
    (φ : (L.withConstants α).Sentence) :
    Independent T φ ↔
      ((fun x : {x : X // ∀ k, x ∈ C k} => f x.val) ⁻¹'
        T.typesWith φ).Nonempty ∧
      (fun x : {x : X // ∀ k, x ∈ C k} => f x.val) ⁻¹'
        T.typesWith φ ≠ Set.univ := by
  exact independence_survives_realization _
    (projection_surjective_of_finite_extension C hclosed f hf hfinite) φ

end Neoplatonic.LTR
