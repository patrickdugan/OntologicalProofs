import Neoplatonic.LTR.ManifestationFragmentNorm

/-!
# Finite recovery through the actual marked Dirac-block endpoints

The concrete syntax-numbered infinite Dirac triple uses the selected
dense completion sequence q and one ordered pair of completed theories
per Hilbert two-point block. Its left endpoint at block Nat.pair k a
equals q k, even when that point coincides with the fallback anchor a.

Thus a finite prefix of q can be transferred to an explicit finite
set of *real marked block indices*. For the minimal finite-fragment
sampling cutoff K(m), a finite block bound J(m) covers every one
of the 2^m truth assignments as a left endpoint.

The verified C*-norm isometry of the finite-fragment observables can
therefore be applied directly to this finite family of actual marked
block endpoints. Proving equality with a FINITE-RANK COMPRESSION of
the full Hilbert operator is the next separate analytic task.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder

/-- For any dense sequence and fallback anchor a, the left endpoint
of the marked pair at Nat.pair k a is exactly the k-th completion. -/
theorem densePairLeft_pair_anchor {X : Type*}
    (q : ℕ → X) (a b k : ℕ) :
    Neoplatonic.LTR.densePairLeft q a b (Nat.pair k a) = q k := by
  classical
  by_cases h : q k = q a
  · simp [Neoplatonic.LTR.densePairLeft, Nat.unpair_pair, h]
  · simp [Neoplatonic.LTR.densePairLeft, Nat.unpair_pair, h]

/-- Every completion from the selected dense sequence occurs as the
left endpoint of an explicitly indexed actual Dirac block. -/
theorem effectiveNullaryMarkedLeft_pair_anchor (k : ℕ) :
    effectiveNullaryMarkedLeft (Nat.pair k effectiveNullaryDenseMarkA) =
      effectiveNullaryDenseSeq k := by
  exact densePairLeft_pair_anchor effectiveNullaryDenseSeq
    effectiveNullaryDenseMarkA effectiveNullaryDenseMarkB k

/-- A finite bound containing the explicit marked block for every
dense-sequence index below the exact m-fragment cutoff K(m). -/
noncomputable def effectiveNullaryMarkedPrefixCutoff (m : ℕ) : ℕ :=
  (Finset.range
    (manifestationPrefixCutoff effectiveNullaryDenseSeq
      effectiveNullaryDenseSeq_dense m)).sup
    (fun k => Nat.pair k effectiveNullaryDenseMarkA + 1)

/-- Every index k < K(m) has its anchor-marked block strictly below J(m). -/
theorem effectiveNullaryMarkedPrefixCutoff_bound
    (m k : ℕ)
    (hk : k < manifestationPrefixCutoff effectiveNullaryDenseSeq
      effectiveNullaryDenseSeq_dense m) :
    Nat.pair k effectiveNullaryDenseMarkA <
      effectiveNullaryMarkedPrefixCutoff m := by
  have h :
      Nat.pair k effectiveNullaryDenseMarkA + 1 ≤
        effectiveNullaryMarkedPrefixCutoff m := by
    change Nat.pair k effectiveNullaryDenseMarkA + 1 ≤
      (Finset.range
        (manifestationPrefixCutoff effectiveNullaryDenseSeq
          effectiveNullaryDenseSeq_dense m)).sup
          (fun j => Nat.pair j effectiveNullaryDenseMarkA + 1)
    exact Finset.le_sup
      (s := Finset.range
        (manifestationPrefixCutoff effectiveNullaryDenseSeq
          effectiveNullaryDenseSeq_dense m))
      (f := fun j : ℕ => (Nat.pair j effectiveNullaryDenseMarkA + 1 : ℕ))
      (Finset.mem_range.mpr hk)
  exact lt_of_lt_of_le (Nat.lt_succ_self _) h

/-- Every m-bit truth assignment is represented by the LEFT endpoint
of one of the first J(m) marked Dirac blocks. -/
theorem effectiveNullaryMarkedPrefixCutoff_covers (m : ℕ) :
    Function.Surjective
      (fun j : Fin (effectiveNullaryMarkedPrefixCutoff m) =>
        manifestationPrefix m (effectiveNullaryMarkedLeft j.val)) := by
  let K := manifestationPrefixCutoff effectiveNullaryDenseSeq
    effectiveNullaryDenseSeq_dense m
  have hcover : Function.Surjective
      (fun i : Fin K => manifestationPrefix m
        (effectiveNullaryDenseSeq i.val)) :=
    manifestationPrefixCutoff_covers effectiveNullaryDenseSeq
      effectiveNullaryDenseSeq_dense m K le_rfl
  intro bits
  obtain ⟨i, hi⟩ := hcover bits
  have hj : Nat.pair i.val effectiveNullaryDenseMarkA <
      effectiveNullaryMarkedPrefixCutoff m :=
    effectiveNullaryMarkedPrefixCutoff_bound m i.val i.isLt
  refine ⟨⟨Nat.pair i.val effectiveNullaryDenseMarkA, hj⟩, ?_⟩
  change manifestationPrefix m
    (effectiveNullaryMarkedLeft
      (Nat.pair i.val effectiveNullaryDenseMarkA)) = bits
  rw [effectiveNullaryMarkedLeft_pair_anchor]
  exact hi

/-- The first J(m) marked blocks necessarily include at least 2^m
indices: the exponential independent-fragment capacity persists. -/
theorem effectiveNullaryMarkedPrefixCutoff_ge_capacity (m : ℕ) :
    2 ^ m ≤ effectiveNullaryMarkedPrefixCutoff m := by
  exact finiteFragment_capacity_lower_bound m
    (effectiveNullaryMarkedPrefixCutoff m)
    (fun i : Fin (effectiveNullaryMarkedPrefixCutoff m) =>
      effectiveNullaryMarkedLeft i.val)
    (effectiveNullaryMarkedPrefixCutoff_covers m)

/-- Exact C*-norm sampling of arbitrary m-fragment complex observables
at the actual left endpoints of finitely many Dirac blocks. -/
theorem effectiveNullary_markedBlock_fragment_norm_isometry
    (m : ℕ) (g : (Fin m → Bool) → ℂ) :
    ‖(manifestationFragmentObservable m g).comp
        (manifestationSampleMap effectiveNullaryMarkedLeft
          (effectiveNullaryMarkedPrefixCutoff m))‖ =
      ‖manifestationFragmentObservable m g‖ := by
  exact manifestationFragment_sample_norm_eq
    m (effectiveNullaryMarkedPrefixCutoff m)
    effectiveNullaryMarkedLeft
    (effectiveNullaryMarkedPrefixCutoff_covers m) g

end Neoplatonic.LTR.Nullary
