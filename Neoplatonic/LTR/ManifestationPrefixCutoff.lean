import Neoplatonic.LTR.ManifestationFiniteRecovery
import Neoplatonic.LTR.NullaryEffectiveMarkedTriple

/-!
# A sharp finite cutoff for every finite logical fragment

The dense enumeration of complete first-order theories used by the
syntax-numbered spectral triple eventually contains all 2^m truth
assignments on the first m independent nullary predicates.

For each m-bit pattern, take the least index at which that pattern
appears in a dense sequence q. Define K(m) as one plus the maximum
of these finitely many first-hit indices.

Lean proves that sampling the first N completions covers the full
m-fragment exactly when N >= K(m), and that K(m) >= 2^m.

The construction is classical. It does not supply a computable rate
for the chosen completion enumeration, nor a global truncation bound
for all logical sentences at once.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder

/-- The finite truth-prefix map is continuous in the Stone topology. -/
theorem manifestationPrefix_continuous (m : ℕ) :
    Continuous (manifestationPrefix m) := by
  apply continuous_pi_iff.mpr
  intro i
  change Continuous (fun p : T.CompleteType Empty => decode p i.val)
  exact (continuous_apply i.val).comp continuous_decode

/-- A dense sequence visits every finite Boolean truth assignment. -/
theorem denseManifestationPrefix_hit
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (m : ℕ) (bits : Fin m → Bool) :
    ∃ j : ℕ, manifestationPrefix m (q j) = bits := by
  let U : Set (T.CompleteType Empty) :=
    {p | manifestationPrefix m p = bits}
  have hopen : IsOpen U := by
    change IsOpen ((manifestationPrefix m) ⁻¹'
      ({bits} : Set (Fin m → Bool)))
    exact (isOpen_discrete _).preimage (manifestationPrefix_continuous m)
  have hne : U.Nonempty := by
    refine ⟨encode (manifestationExtend m bits), ?_⟩
    exact manifestationPrefix_encode_extend m bits
  obtain ⟨j, hj⟩ := hq.exists_mem_open hopen hne
  exact ⟨j, hj⟩

/-- Least index at which the chosen dense sequence first sees a bit pattern. -/
noncomputable def manifestationPrefixFirstHit
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (m : ℕ) (bits : Fin m → Bool) : ℕ := by
  classical
  exact Nat.find (denseManifestationPrefix_hit q hq m bits)

theorem manifestationPrefixFirstHit_spec
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (m : ℕ) (bits : Fin m → Bool) :
    manifestationPrefix m (q (manifestationPrefixFirstHit q hq m bits)) =
      bits := by
  classical
  unfold manifestationPrefixFirstHit
  exact Nat.find_spec (denseManifestationPrefix_hit q hq m bits)

/-- The finite-fragment cutoff is one plus the latest first appearance
of any m-bit assignment. -/
noncomputable def manifestationPrefixCutoff
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (m : ℕ) : ℕ := by
  classical
  exact (Finset.univ : Finset (Fin m → Bool)).sup
    (fun bits => manifestationPrefixFirstHit q hq m bits + 1)

theorem manifestationPrefixCutoff_bound
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (m : ℕ) (bits : Fin m → Bool) :
    manifestationPrefixFirstHit q hq m bits + 1 ≤
      manifestationPrefixCutoff q hq m := by
  classical
  change manifestationPrefixFirstHit q hq m bits + 1 ≤
    (Finset.univ : Finset (Fin m → Bool)).sup
      (fun bits => manifestationPrefixFirstHit q hq m bits + 1)
  exact Finset.le_sup
    (s := (Finset.univ : Finset (Fin m → Bool)))
    (f := fun b : Fin m → Bool =>
      (manifestationPrefixFirstHit q hq m b + 1 : ℕ))
    (Finset.mem_univ bits)

/-- Every sample of depth at least K(m) realizes each prefix,
hence the entire m-proposition Boolean fragment is visible. -/
theorem manifestationPrefixCutoff_covers
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (m N : ℕ) (hN : manifestationPrefixCutoff q hq m ≤ N) :
    Function.Surjective (fun i : Fin N => manifestationPrefix m (q i.val)) := by
  intro bits
  let j := manifestationPrefixFirstHit q hq m bits
  have hj : manifestationPrefix m (q j) = bits :=
    manifestationPrefixFirstHit_spec q hq m bits
  have hlt : j < N :=
    lt_of_lt_of_le (Nat.lt_succ_self j)
      ((manifestationPrefixCutoff_bound q hq m bits).trans hN)
  exact ⟨⟨j, hlt⟩, hj⟩

/-- Conversely, any covering prefix contains the first appearance
of every pattern, so N must be at least the exact K(m). -/
theorem manifestationPrefixCutoff_le_of_covers
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (m N : ℕ)
    (hcover : Function.Surjective
      (fun i : Fin N => manifestationPrefix m (q i.val))) :
    manifestationPrefixCutoff q hq m ≤ N := by
  classical
  change (Finset.univ : Finset (Fin m → Bool)).sup
    (fun bits => manifestationPrefixFirstHit q hq m bits + 1) ≤ N
  apply Finset.sup_le
  intro bits _
  obtain ⟨i, hi⟩ := hcover bits
  have hfirst : manifestationPrefixFirstHit q hq m bits ≤ i.val := by
    unfold manifestationPrefixFirstHit
    exact Nat.find_min' (denseManifestationPrefix_hit q hq m bits) hi
  exact Nat.succ_le_iff.mpr (lt_of_le_of_lt hfirst i.isLt)

/-- K(m) exactly characterizes finite-fragment coverage. -/
theorem manifestationPrefixCutoff_iff_covers
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (m N : ℕ) :
    manifestationPrefixCutoff q hq m ≤ N ↔
      Function.Surjective
        (fun i : Fin N => manifestationPrefix m (q i.val)) := by
  constructor
  · exact manifestationPrefixCutoff_covers q hq m N
  · exact manifestationPrefixCutoff_le_of_covers q hq m N

/-- The exact cutoff respects the combinatorial capacity bound. -/
theorem manifestationPrefixCutoff_ge_capacity
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (m : ℕ) :
    2 ^ m ≤ manifestationPrefixCutoff q hq m := by
  exact finiteFragment_capacity_lower_bound m
    (manifestationPrefixCutoff q hq m)
    (fun i : Fin (manifestationPrefixCutoff q hq m) => q i.val)
    (manifestationPrefixCutoff_covers q hq m
      (manifestationPrefixCutoff q hq m) le_rfl)

/-- Uniform-on-fragment coverage and the exponential lower bound,
specialized to the dense sequence of the concrete spectral triple. -/
theorem effectiveNullaryDensePrefixCutoff_certificate (m : ℕ) :
    let q := effectiveNullaryDenseSeq
    let K := manifestationPrefixCutoff q effectiveNullaryDenseSeq_dense m
    2 ^ m ≤ K ∧
      ∀ N ≥ K,
        Function.Surjective
          (fun i : Fin N => manifestationPrefix m (q i.val)) := by
  dsimp
  constructor
  · exact manifestationPrefixCutoff_ge_capacity
      effectiveNullaryDenseSeq effectiveNullaryDenseSeq_dense m
  · intro N hN
    exact manifestationPrefixCutoff_covers
      effectiveNullaryDenseSeq effectiveNullaryDenseSeq_dense m N hN

end Neoplatonic.LTR.Nullary
