import Neoplatonic.LTR.ManifestationDiagonal
import Neoplatonic.LTR.NullaryEffectiveHilbertOperators
import Neoplatonic.LTR.LogicalHilbertNormGap

/-!
# A literal finite-sample separating sentence and its Hilbert norm gap

The v0.1 diagonal produced a nonempty clopen set missing every member
of a finite sample of genuine complete first-order theories.
This module constructs an actual expanded-language first-order sentence:
a finite conjunction of positive or negative lifted nullary atoms.

Its truth locus is exactly the v0.1 cylinder. The established faithful
infinite-dimensional spectral triple assigns a named nonzero orthogonal
projection to this sentence, of norm exactly one. Every finite sample
evaluates the same sentence as false.

The sample may contain repeated points; n=0 gives the tautology.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Theory

/-- The i-th literal has truth value opposite that of sample i. -/
noncomputable def manifestationLiteral (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) (i : Fin n) :
    L[[Empty]].Sentence :=
  if decode (samples i) i.val = true
  then (liftedAtom i.val).not
  else liftedAtom i.val

/-- Each literal holds exactly when its Boolean coordinate disagrees
with the corresponding sampled completion. -/
theorem manifestationLiteral_mem_iff (n : ℕ)
    (samples : Fin n → T.CompleteType Empty)
    (i : Fin n) (p : T.CompleteType Empty) :
    manifestationLiteral n samples i ∈ p ↔
      decode p i.val = !(decode (samples i) i.val) := by
  classical
  have hp : (liftedAtom i.val ∈ p) ↔ decode p i.val = true := by
    simp [decode]
  have hn : ((liftedAtom i.val).not ∈ p) ↔ decode p i.val = false := by
    rw [p.not_mem_iff]
    simp [decode]
  cases hs : decode (samples i) i.val with
  | false =>
      simpa [manifestationLiteral, hs] using hp
  | true =>
      simpa [manifestationLiteral, hs] using hn

/-- The finite set of required literals. Any repetitions caused by
syntactic equivalence are harmless. -/
noncomputable def manifestationLiterals (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    Finset L[[Empty]].Sentence := by
  classical
  exact Finset.univ.image (manifestationLiteral n samples)

/-- An actual first-order sentence, formed as the finite conjunction
of the required literals and top (the empty conjunction). -/
noncomputable def manifestationSentence (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) : L[[Empty]].Sentence :=
  (manifestationLiterals n samples).toList.foldr (fun φ ψ => φ ⊓ ψ) ⊤

/-- Finite conjunction membership, proved directly from the Stone-space
meet and top laws (independent of Mathlib's later convenience lemmas). -/
private theorem foldrInf_mem_iff (p : T.CompleteType Empty)
    (l : List L[[Empty]].Sentence) :
    l.foldr (fun φ ψ => φ ⊓ ψ) ⊤ ∈ p ↔
      ∀ φ ∈ l, φ ∈ p := by
  induction l with
  | nil =>
      have htop : (⊤ : L[[Empty]].Sentence) ∈ p := by
        have h : p ∈ T.typesWith (⊤ : L[[Empty]].Sentence) := by
          rw [CompleteType.typesWith_top]
          exact Set.mem_univ _
        exact h
      simpa using htop
  | cons φ fs ih =>
      have hmeet :
          (φ ⊓ fs.foldr (fun x y => x ⊓ y) ⊤) ∈ p ↔
            φ ∈ p ∧ fs.foldr (fun x y => x ⊓ y) ⊤ ∈ p := by
        change p ∈ T.typesWith (φ ⊓ fs.foldr (fun x y => x ⊓ y) ⊤) ↔
          p ∈ T.typesWith φ ∩
            T.typesWith (fs.foldr (fun x y => x ⊓ y) ⊤)
        rw [CompleteType.typesWith_inf]
      rw [hmeet, ih]
      simp

/-- The sentence belongs to a complete type precisely when every
opposite-coordinate literal belongs to it. -/
theorem manifestationSentence_mem_iff (n : ℕ)
    (samples : Fin n → T.CompleteType Empty)
    (p : T.CompleteType Empty) :
    manifestationSentence n samples ∈ p ↔
      ∀ i : Fin n, manifestationLiteral n samples i ∈ p := by
  classical
  unfold manifestationSentence
  rw [foldrInf_mem_iff]
  constructor
  · intro h i
    apply h
    exact Finset.mem_toList.mpr
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  · intro h φ hφ
    have hφ' : φ ∈ manifestationLiterals n samples :=
      Finset.mem_toList.mp hφ
    rcases Finset.mem_image.mp hφ' with ⟨i, _, hi⟩
    rw [← hi]
    exact h i

/-- The named first-order sentence realizes exactly the separating
clopen cylinder from the v0.1 theorem. -/
theorem manifestationSentence_locus (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    T.typesWith (manifestationSentence n samples) =
      manifestationCylinder n samples := by
  ext p
  change manifestationSentence n samples ∈ p ↔
    ∀ i : Fin n,
      decode p i.val = !(decode (samples i) i.val)
  rw [manifestationSentence_mem_iff]
  constructor
  · intro h i
    exact (manifestationLiteral_mem_iff n samples i p).mp (h i)
  · intro h i
    exact (manifestationLiteral_mem_iff n samples i p).mpr (h i)

/-- The explicit first-order sentence holds in the diagonal completion. -/
theorem manifestationSentence_diagonal_true (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    manifestationSentence n samples ∈
      encode (manifestationDiagonalBits n samples) := by
  have h : encode (manifestationDiagonalBits n samples) ∈
    T.typesWith (manifestationSentence n samples) := by
    rw [manifestationSentence_locus]
    exact manifestationDiagonal_mem n samples
  exact h

/-- Each sample individually refutes the same concrete sentence. -/
theorem manifestationSentence_samples_false (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) (i : Fin n) :
    manifestationSentence n samples ∉ samples i := by
  intro hmem
  have h : samples i ∈ T.typesWith (manifestationSentence n samples) := hmem
  rw [manifestationSentence_locus] at h
  exact manifestationCylinder_misses n samples i h

/-- A named Boolean projection survives with norm one in C(X, C). -/
theorem manifestationSentence_complex_norm_one (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    ‖Neoplatonic.LTR.complexLogicalProjection (T := T)
      (manifestationSentence n samples)‖ = 1 := by
  rw [Neoplatonic.LTR.complexLogicalProjection_norm_eq_real]
  apply Neoplatonic.LTR.logicalProjection_norm_one_of_nonempty
  exact ⟨encode (manifestationDiagonalBits n samples),
    manifestationSentence_diagonal_true n samples⟩

/-- The same truth sentence is a norm-one operator in the concrete
infinite-dimensional, syntax-numbered Hilbert spectral triple. -/
theorem effectiveNullary_manifestationHilbert_norm_one (n : ℕ)
    (samples : Fin n → T.CompleteType Empty) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    ‖effectiveNullaryStoneSpectralTriple.representation
      (Neoplatonic.LTR.complexLogicalProjection (T := T)
        (manifestationSentence n samples))‖ = 1 := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  let S := effectiveNullaryStoneSpectralTriple
  let f := Neoplatonic.LTR.complexLogicalProjection (T := T)
      (manifestationSentence n samples)
  have hf : ‖f‖ = 1 := manifestationSentence_complex_norm_one n samples
  have hnonzero : S.representation f ≠ 0 := by
    intro hz
    have hzero : f = 0 := S.representation_faithful (by
      simpa only [map_zero] using hz)
    rw [hzero, norm_zero] at hf
    norm_num at hf
  have hproj : S.representation f * S.representation f =
      S.representation f ∧
      star (S.representation f) = S.representation f := by
    exact effectiveNullary_sentence_hilbertProjection
      (manifestationSentence n samples)
  have hnorm : ‖S.representation f‖ * ‖S.representation f‖ =
      ‖S.representation f‖ := by
    calc
      ‖S.representation f‖ * ‖S.representation f‖ =
          ‖star (S.representation f) * S.representation f‖ :=
        (CStarRing.norm_star_mul_self).symm
      _ = ‖S.representation f‖ := by rw [hproj.2, hproj.1]
  have hfactor : ‖S.representation f‖ *
      (‖S.representation f‖ - 1) = 0 := by
    nlinarith [hnorm]
  rcases mul_eq_zero.mp hfactor with hz | hone
  · exact False.elim (hnonzero (norm_eq_zero.mp hz))
  · exact sub_eq_zero.mp hone

end Neoplatonic.LTR.Nullary
