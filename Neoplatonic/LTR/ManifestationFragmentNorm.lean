import Neoplatonic.LTR.ManifestationPrefixCutoff
import Neoplatonic.LTR.ComplexConservativeSpectral

/-!
# Exact finite-fragment C*-norm recovery

A finite m-generator Boolean fragment of the nullary theory has
2^m possible complete truth patterns. Every complex-valued function
on these patterns induces a continuous observable on the actual
Stone space of all completed theories.

When a finite sample realizes every m-bit pattern, evaluation
on that sample preserves the norm of EVERY such observable.
This is stronger than recovering individual 0/1 sentence projections:
it includes arbitrary complex linear combinations and products
of all sentence observables in the finite fragment.

At the exact dense-prefix cutoff K(m), finite sampling is isometric
on the complete finite-fragment commutative C*-algebra.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder

/-- A complex-valued observable determined by the first m Boolean
truth bits of a genuine complete first-order theory. -/
noncomputable def manifestationFragmentObservable (m : ℕ)
    (g : (Fin m → Bool) → ℂ) :
    C(T.CompleteType Empty, ℂ) :=
  ⟨fun p => g (manifestationPrefix m p),
    (continuous_of_discreteTopology).comp
      (manifestationPrefix_continuous m)⟩

/-- Evaluate a complete type at finitely many chosen completed theories. -/
noncomputable def manifestationSampleMap
    (q : ℕ → T.CompleteType Empty) (N : ℕ) :
    C(Fin N, T.CompleteType Empty) :=
  ⟨fun i => q i.val, continuous_of_discreteTopology⟩

/-- A uniform bound checked on a fragment-complete finite sample is
equivalent to the true C*-norm bound on the full Stone space. -/
theorem manifestationFragment_norm_le_iff_samples
    (m N : ℕ) (q : ℕ → T.CompleteType Empty)
    (hcover : Function.Surjective
      (fun i : Fin N => manifestationPrefix m (q i.val)))
    (g : (Fin m → Bool) → ℂ) (B : ℝ) (hB : 0 ≤ B) :
    ‖manifestationFragmentObservable m g‖ ≤ B ↔
      ∀ i : Fin N, ‖g (manifestationPrefix m (q i.val))‖ ≤ B := by
  constructor
  · intro h i
    calc
      ‖g (manifestationPrefix m (q i.val))‖ =
          ‖manifestationFragmentObservable m g (q i.val)‖ := rfl
      _ ≤ ‖manifestationFragmentObservable m g‖ :=
        (manifestationFragmentObservable m g).norm_coe_le_norm (q i.val)
      _ ≤ B := h
  · intro h
    apply (ContinuousMap.norm_le _ hB).2
    intro p
    obtain ⟨i, hi⟩ := hcover (manifestationPrefix m p)
    change ‖g (manifestationPrefix m p)‖ ≤ B
    rw [← hi]
    exact h i

/-- Exact isometry of finite point-evaluation for all complex observables
factoring through the m-bit prefix. -/
theorem manifestationFragment_sample_norm_eq
    (m N : ℕ) (q : ℕ → T.CompleteType Empty)
    (hcover : Function.Surjective
      (fun i : Fin N => manifestationPrefix m (q i.val)))
    (g : (Fin m → Bool) → ℂ) :
    ‖(manifestationFragmentObservable m g).comp
        (manifestationSampleMap q N)‖ =
      ‖manifestationFragmentObservable m g‖ := by
  let gC : C((Fin m → Bool), ℂ) :=
    ⟨g, continuous_of_discreteTopology⟩
  let pref : C(T.CompleteType Empty, (Fin m → Bool)) :=
    ⟨manifestationPrefix m, manifestationPrefix_continuous m⟩
  let sampledPref : C(Fin N, (Fin m → Bool)) :=
    ⟨(fun i => manifestationPrefix m (q i.val)),
      continuous_of_discreteTopology⟩
  have hsample : ‖gC.comp sampledPref‖ = ‖gC‖ :=
    Neoplatonic.LTR.continuous_surjection_preserves_complex_norm
      sampledPref hcover gC
  have hfull : ‖gC.comp pref‖ = ‖gC‖ :=
    Neoplatonic.LTR.continuous_surjection_preserves_complex_norm
      pref (manifestationPrefix_surjective m) gC
  calc
    ‖(manifestationFragmentObservable m g).comp
        (manifestationSampleMap q N)‖ =
        ‖gC.comp sampledPref‖ := by
          rfl
    _ = ‖gC‖ := hsample
    _ = ‖manifestationFragmentObservable m g‖ := by
          rw [← hfull]
          rfl

/-- The actual classically chosen dense sequence gives exact
norm recovery at every cutoff N >= K(m). -/
theorem effectiveNullary_fragment_norm_isometry
    (m N : ℕ)
    (hN : manifestationPrefixCutoff effectiveNullaryDenseSeq
      effectiveNullaryDenseSeq_dense m ≤ N)
    (g : (Fin m → Bool) → ℂ) :
    ‖(manifestationFragmentObservable m g).comp
        (manifestationSampleMap effectiveNullaryDenseSeq N)‖ =
      ‖manifestationFragmentObservable m g‖ := by
  exact manifestationFragment_sample_norm_eq
    m N effectiveNullaryDenseSeq
    (manifestationPrefixCutoff_covers
      effectiveNullaryDenseSeq effectiveNullaryDenseSeq_dense m N hN) g

end Neoplatonic.LTR.Nullary
