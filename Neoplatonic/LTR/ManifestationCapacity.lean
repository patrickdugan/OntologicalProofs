import Neoplatonic.LTR.ManifestationSentence
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact capacity of finite Boolean fragments in the nullary Stone space

The first m independent predicates define 2^m distinct truth
assignments. Evaluating a complete theory at those m predicates
gives its finite prefix. A family of n completed theories that
realizes every such prefix has n >= 2^m; an explicitly indexed
canonical sample of size 2^m attains this bound.

The result counts faithful point evaluations on the full
finite-fragment Boolean algebra. It does not assign physical
dimension, memory or spiritual attributes to finite beings.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder

/-- The m-coordinate truth assignment of an actual complete type. -/
noncomputable def manifestationPrefix (m : ℕ)
    (p : T.CompleteType Empty) : Fin m → Bool :=
  fun i => decode p i.val

/-- Extend any m-bit prefix by false values on the remaining atoms. -/
def manifestationExtend (m : ℕ) (bits : Fin m → Bool) : ℕ → Bool :=
  fun k => if h : k < m then bits ⟨k, h⟩ else false

/-- The actual complete type of an explicitly extended prefix realizes
that prefix exactly. -/
theorem manifestationPrefix_encode_extend (m : ℕ) (bits : Fin m → Bool) :
    manifestationPrefix m (encode (manifestationExtend m bits)) = bits := by
  funext i
  change decode (encode (manifestationExtend m bits)) i.val = bits i
  rw [decode_encode]
  simp [manifestationExtend, i.isLt]

/-- Every finite Boolean truth assignment appears in a genuine model. -/
theorem manifestationPrefix_surjective (m : ℕ) :
    Function.Surjective (manifestationPrefix m) := by
  intro bits
  exact ⟨encode (manifestationExtend m bits),
    manifestationPrefix_encode_extend m bits⟩

/-- There are exactly 2^m m-bit assignments, with an explicit finite index. -/
noncomputable def manifestationBitsEquivFin (m : ℕ) :
    Fin (2 ^ m) ≃ (Fin m → Bool) :=
  (Fintype.equivFinOfCardEq (α := Fin m → Bool)
    (n := 2 ^ m) (by simp)).symm

/-- One genuine complete type for each possible m-bit truth assignment. -/
noncomputable def manifestationCanonicalSamples (m : ℕ) :
    Fin (2 ^ m) → T.CompleteType Empty :=
  fun i => encode (manifestationExtend m (manifestationBitsEquivFin m i))

/-- Canonical samples visit each of the 2^m finite truth assignments. -/
theorem manifestationCanonicalSamples_prefix (m : ℕ)
    (i : Fin (2 ^ m)) :
    manifestationPrefix m (manifestationCanonicalSamples m i) =
      manifestationBitsEquivFin m i := by
  exact manifestationPrefix_encode_extend m (manifestationBitsEquivFin m i)

/-- The canonical sample has exact finite-fragment coverage. -/
theorem manifestationCanonicalSamples_cover (m : ℕ) :
    Function.Surjective
      (fun i : Fin (2 ^ m) =>
        manifestationPrefix m (manifestationCanonicalSamples m i)) := by
  intro bits
  obtain ⟨i, hi⟩ := (manifestationBitsEquivFin m).surjective bits
  refine ⟨i, ?_⟩
  simpa [manifestationCanonicalSamples_prefix] using hi

/-- Any finite family that observes all m-bit assignments must contain
at least 2^m points, allowing repetitions in the original family. -/
theorem finiteFragment_capacity_lower_bound (m n : ℕ)
    (samples : Fin n → T.CompleteType Empty)
    (hcover : Function.Surjective
      (fun i : Fin n => manifestationPrefix m (samples i))) :
    2 ^ m ≤ n := by
  have hcard : Fintype.card (Fin m → Bool) ≤ Fintype.card (Fin n) :=
    Fintype.card_le_of_surjective _ hcover
  simpa [Fintype.card_fun] using hcard

/-- The lower bound is attained. This certifies the exact
point-sampling capacity of an m-generator Boolean fragment. -/
theorem finiteFragment_capacity_exact (m : ℕ) :
    (∃ samples : Fin (2 ^ m) → T.CompleteType Empty,
      Function.Surjective
        (fun i : Fin (2 ^ m) => manifestationPrefix m (samples i))) ∧
    ∀ (n : ℕ) (samples : Fin n → T.CompleteType Empty),
      Function.Surjective
        (fun i : Fin n => manifestationPrefix m (samples i)) →
      2 ^ m ≤ n := by
  constructor
  · exact ⟨manifestationCanonicalSamples m,
      manifestationCanonicalSamples_cover m⟩
  · intro n samples h
    exact finiteFragment_capacity_lower_bound m n samples h

/-- For fewer than 2^m samples, an m-bit assignment is missing.
This is a sharper finite-fragment obstruction than the original
n-literal diagonal, at a shorter distinguishing word length. -/
theorem finiteFragment_unseen_assignment (m n : ℕ)
    (samples : Fin n → T.CompleteType Empty) (hsmall : n < 2 ^ m) :
    ∃ bits : Fin m → Bool,
      ∀ i : Fin n, manifestationPrefix m (samples i) ≠ bits := by
  by_contra hnone
  push_neg at hnone
  have hcover : Function.Surjective
      (fun i : Fin n => manifestationPrefix m (samples i)) := by
    intro bits
    obtain ⟨i, hi⟩ := hnone bits
    exact ⟨i, hi⟩
  exact (Nat.not_le_of_gt hsmall)
    (finiteFragment_capacity_lower_bound m n samples hcover)

end Neoplatonic.LTR.Nullary
