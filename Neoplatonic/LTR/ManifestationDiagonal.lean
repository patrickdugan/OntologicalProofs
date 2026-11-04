import Neoplatonic.LTR.NullaryTopology

/-!
# Finite manifestation obstruction for the concrete nullary Stone space

The concrete one-axiom nullary first-order theory has a complete-type
space homeomorphic to Cantor space. Given any finite list of genuine
complete theories, we construct a cylinder whose first n truth bits
diagonalize against that list. The cylinder is clopen and nonempty,
yet all sampled completions miss it.

This is a semantic obstruction to faithful FINITE POINT-SAMPLING of the
labelled Stone space. It is not a statement about arbitrary nonlinear
embodiments, nor does it construct a classifying topos or a physical model.

The construction uses the existing noncomputable complete-type decode.
The finite Boolean diagonal itself is structurally explicit.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- A Boolean stream which disagrees with sample i at coordinate i
for each i in Fin n. Its tail is fixed to false. -/
noncomputable def manifestationDiagonalBits (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) : ℕ → Bool :=
  fun k => if h : k < n then !(decode (samples ⟨k, h⟩) k) else false

/-- The n-literal coordinate cylinder targeted by the diagonal stream.
Each clause fixes exactly one nullary truth coordinate. -/
noncomputable def manifestationCylinder (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    Set (T.CompleteType Empty) :=
  {p | ∀ i : Fin n,
    decode p i.val = !(decode (samples i) i.val)}

/-- A genuine complete first-order theory satisfies the entire cylinder. -/
theorem manifestationDiagonal_mem (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    encode (manifestationDiagonalBits n samples) ∈
      manifestationCylinder n samples := by
  change ∀ i : Fin n,
    decode (encode (manifestationDiagonalBits n samples)) i.val =
      !(decode (samples i) i.val)
  intro i
  rw [decode_encode]
  rcases i with ⟨k, hk⟩
  simp [manifestationDiagonalBits, hk]

/-- Every listed complete theory fails its own diagonal coordinate. -/
theorem manifestationCylinder_misses (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) (i : Fin n) :
    samples i ∉ manifestationCylinder n samples := by
  intro h
  have hi : decode (samples i) i.val =
      !(decode (samples i) i.val) := h i
  cases hb : decode (samples i) i.val <;> simp [hb] at hi

/-- A finite intersection of Boolean coordinate fibres is clopen. -/
theorem manifestationCylinder_isClopen (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    IsClopen (manifestationCylinder n samples) := by
  change IsClopen (⋂ i : Fin n,
    {p : T.CompleteType Empty |
      decode p i.val = !(decode (samples i) i.val)})
  apply isClopen_iInter_of_finite
  intro i
  have hc : Continuous (fun p : T.CompleteType Empty => decode p i.val) :=
    (continuous_apply i.val).comp continuous_decode
  change IsClopen
    ((fun p : T.CompleteType Empty => decode p i.val) ⁻¹'
      ({!(decode (samples i) i.val)} : Set Bool))
  exact (isClopen_discrete _).preimage hc

/-- No finite family of points hits every nonempty clopen truth locus
of the actual complete-type space. The separating witness is a cylinder
defined by n atomic truth bits. -/
theorem finiteManifestation_obstruction (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    ∃ U : Set (T.CompleteType Empty),
      IsClopen U ∧ U.Nonempty ∧
      ∀ i : Fin n, samples i ∉ U := by
  refine ⟨manifestationCylinder n samples,
    manifestationCylinder_isClopen n samples, ?_, ?_⟩
  · exact ⟨encode (manifestationDiagonalBits n samples),
      manifestationDiagonal_mem n samples⟩
  · exact manifestationCylinder_misses n samples

/-- Finite evaluation of clopen truth loci cannot reflect the
nonemptiness predicate for every clopen set. -/
theorem finiteManifestation_not_conservative (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    ¬ ∀ U : Set (T.CompleteType Empty),
      IsClopen U → (U.Nonempty ↔ ∃ i : Fin n, samples i ∈ U) := by
  intro hall
  obtain ⟨U, hclopen, hnonempty, hmiss⟩ :=
    finiteManifestation_obstruction n samples
  obtain ⟨i, hi⟩ := (hall U hclopen).mp hnonempty
  exact (hmiss i) hi

end Neoplatonic.LTR.Nullary
