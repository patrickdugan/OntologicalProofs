import Mathlib

/-!
# LTR-UG-03: an exact observable-aliasing obstruction to semiconjugacy

If two microstates have the same proposed observation but different future
readouts, a deterministic quotient and macro transition cannot reproduce
both. The triangle inequality also gives a sharp factor-two bound on the
worst prediction error of any proposed macrostate decoder.

This is a general elementary statement; applying it to a frozen neural
checkpoint requires independently measured finite-pair evidence.
-/

namespace Neoplatonic.LTR.GoalQuotientAliasing

universe u v w x

variable {State : Type u} {Obs : Type v} {Latent : Type w} {Output : Type x}

/-- A deterministic decoder cannot distinguish identical observations. -/
theorem same_observation_same_prediction
    (observe : State → Obs) (q : Obs → Latent) (F : Latent → Latent)
    (decode : Latent → Output) {a b : State}
    (hab : observe a = observe b) :
    decode (F (q (observe a))) = decode (F (q (observe b))) := by
  rw [hab]

/-- A pair with identical observation and unequal future outputs excludes any
globally exact deterministic latent predictor from that observation. -/
theorem unequal_future_forbids_exact_factorization
    (observe : State → Obs) (q : Obs → Latent) (F : Latent → Latent)
    (decode : Latent → Output) (future : State → Output)
    {a b : State} (hab : observe a = observe b)
    (hneq : future a ≠ future b) :
    ¬ ∀ s : State, decode (F (q (observe s))) = future s := by
  intro h
  apply hneq
  calc
    future a = decode (F (q (observe a))) := (h a).symm
    _ = decode (F (q (observe b))) :=
      same_observation_same_prediction observe q F decode hab
    _ = future b := h b

variable [NormedAddCommGroup Output]

/-- Quantitative aliasing: both decoder errors must jointly cover the actual
future-output gap between two observationally equivalent microstates. -/
theorem aliasing_error_sum_lower_bound
    (observe : State → Obs) (q : Obs → Latent) (F : Latent → Latent)
    (decode : Latent → Output) (future : State → Output)
    {a b : State} (hab : observe a = observe b) :
    ‖future a - future b‖ ≤
      ‖future a - decode (F (q (observe a)))‖ +
      ‖future b - decode (F (q (observe b)))‖ := by
  have hp := same_observation_same_prediction observe q F decode hab
  let p := decode (F (q (observe a)))
  calc
    ‖future a - future b‖ =
        ‖(future a - p) + (p - future b)‖ := by congr 1; abel
    _ ≤ ‖future a - p‖ + ‖p - future b‖ := norm_add_le _ _
    _ = ‖future a - decode (F (q (observe a)))‖ +
        ‖future b - decode (F (q (observe b)))‖ := by
      rw [norm_sub_rev p (future b)]
      simp only [p, hp]

/-- At least one member of an observational alias pair incurs prediction
error at least half the future-output separation. -/
theorem aliasing_max_error_lower_bound
    (observe : State → Obs) (q : Obs → Latent) (F : Latent → Latent)
    (decode : Latent → Output) (future : State → Output)
    {a b : State} (hab : observe a = observe b) :
    ‖future a - future b‖ / (2 : ℝ) ≤
      max (‖future a - decode (F (q (observe a)))‖)
          (‖future b - decode (F (q (observe b)))‖) := by
  have h := aliasing_error_sum_lower_bound observe q F decode future hab
  have ha : ‖future a - decode (F (q (observe a)))‖ ≤
      max (‖future a - decode (F (q (observe a)))‖)
          (‖future b - decode (F (q (observe b)))‖) :=
    le_max_left _ _
  have hb : ‖future b - decode (F (q (observe b)))‖ ≤
      max (‖future a - decode (F (q (observe a)))‖)
          (‖future b - decode (F (q (observe b)))‖) :=
    le_max_right _ _
  linarith

end Neoplatonic.LTR.GoalQuotientAliasing
