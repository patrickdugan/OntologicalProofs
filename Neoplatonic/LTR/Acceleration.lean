import Neoplatonic.LTR.DepthProfile

/-!
# Computable prefix maps with unbounded geometric distortion

A stream transformer uses the source bit at 2n after a monotone signal
becomes true, and the bit at n before that signal. A time-bounded halting
signal is a uniformly computable instance. The theorem below identifies
finite additive delay exactly with permanent nonactivation.

The undecidability corollary takes the noncomputability of the external
halting complement explicitly as an input. It does not define or prove
the arithmetic halting theorem in Lean.
-/

namespace Neoplatonic.LTR

/-- Reading x(2n) after signal H(n) becomes true. -/
def acceleratedStream (H : ℕ → Bool)
    (x : ℕ → Bool) (n : ℕ) : Bool :=
  match H n with
  | true => x (2 * n)
  | false => x n

/-- A signal that never activates gives the identity translation. -/
theorem acceleratedStream_id (H : ℕ → Bool)
    (hne : ∀ n, H n = false) :
    acceleratedStream H = id := by
  funext x n
  simp [acceleratedStream, hne n]

/-- In the permanently inactive case the translation has zero delay. -/
theorem acceleratedStream_zero_delay (H : ℕ → Bool)
    (hne : ∀ n, H n = false) :
    TranslationDelay (fun x : ℕ → Bool => x)
      (fun x : ℕ → Bool => x) (acceleratedStream H) 0 := by
  rw [acceleratedStream_id H hne]
  exact translationDelay_id _

/-- Any eventual monotone activation makes additive delay unbounded.
The witness changes a single bit at 2n, while exposing the change at n. -/
theorem acceleratedStream_no_delay (H : ℕ → Bool)
    (hmono : ∀ a b, a ≤ b → H a = true → H b = true)
    (hact : ∃ n, H n = true) (c : ℕ) :
    ¬ TranslationDelay (fun x : ℕ → Bool => x)
      (fun x : ℕ → Bool => x) (acceleratedStream H) c := by
  intro hdelay
  obtain ⟨n₀, hn₀⟩ := hact
  let n := n₀ + c + 2
  have hn : H n = true := hmono n₀ n (by dsimp [n]; omega) hn₀
  let x : ℕ → Bool := fun _ => false
  let y : ℕ → Bool := fun k => decide (k = 2 * n)
  have hp : PrefixAgreement (fun z : ℕ → Bool => z) (n + 1 + c) x y := by
    intro k hk
    have hne : k ≠ 2 * n := by dsimp [n] at *; omega
    simp [x, y, hne]
  have hout := hdelay (n + 1) x y hp n (by omega)
  have hx : acceleratedStream H x n = false := by
    simp [acceleratedStream, hn, x]
  have hy : acceleratedStream H y n = true := by
    simp [acceleratedStream, hn, y]
  change acceleratedStream H x n = acceleratedStream H y n at hout
  rw [hx, hy] at hout
  cases hout

/-- A global additive delay exists exactly when the monotone signal
never activates. Pointwise computability of the stream map alone does not
ensure a uniform additive filtration bound. -/
theorem acceleratedStream_finite_delay_iff (H : ℕ → Bool)
    (hmono : ∀ a b, a ≤ b → H a = true → H b = true) :
    (∃ c, TranslationDelay (fun x : ℕ → Bool => x)
      (fun x : ℕ → Bool => x) (acceleratedStream H) c) ↔
      ∀ n, H n = false := by
  constructor
  · rintro ⟨c, hc⟩ n
    cases hv : H n with
    | false => rfl
    | true =>
        have hbad := acceleratedStream_no_delay H hmono ⟨n, hv⟩ c
        exact False.elim (hbad hc)
  · intro hn
    exact ⟨0, acceleratedStream_zero_delay H hn⟩

/-- An explicit conditional reduction: if the no-activation predicate for
a family of monotone signals is noncomputable, the associated finite-delay
predicate is noncomputable. For H(e,n) = 'machine e halts by stage n',
this is the usual halting problem. -/
theorem no_uniform_finite_delay_decider
    (H : ℕ → ℕ → Bool)
    (hmono : ∀ e a b, a ≤ b → H e a = true → H e b = true)
    (h : ¬ ComputablePred (fun e => ∀ n, H e n = false)) :
    ¬ ComputablePred (fun e =>
      ∃ c, TranslationDelay (fun x : ℕ → Bool => x)
        (fun x : ℕ → Bool => x) (acceleratedStream (H e)) c) := by
  have heq : (fun e =>
      ∃ c, TranslationDelay (fun x : ℕ → Bool => x)
        (fun x : ℕ → Bool => x) (acceleratedStream (H e)) c) =
      (fun e => ∀ n, H e n = false) := by
    funext e
    exact propext (acceleratedStream_finite_delay_iff (H e) (hmono e))
  intro hc
  rw [heq] at hc
  exact h hc

end Neoplatonic.LTR
