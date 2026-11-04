/-!
The E3/E4/E5 information bottleneck. The mathematical fact is about
functions of insufficient representations, not about God's knowledge.
-/
import Init
namespace DivineElegance
universe u v w

/-- A view collision with different required answers blocks a perfect decoder. -/
theorem no_perfect_decoder {Full : Type u} {View : Type v} {Answer : Type w}
    (encode : Full → View) (required : Full → Answer)
    (x y : Full) (sameView : encode x = encode y)
    (differentDuty : required x ≠ required y) :
    ¬ (∃ f : View → Answer, ∀ z, f (encode z) = required z) := by
  intro h
  cases h with
  | intro f hf =>
    have sameOutput : f (encode x) = f (encode y) :=
      congrArg f sameView
    have sameDuty : required x = required y := by
      calc
        required x = f (encode x) := (hf x).symm
        _ = f (encode y) := sameOutput
        _ = required y := hf y
    exact differentDuty sameDuty

structure MoralRecord where
  forgiven : Bool
  victimClaimSettled : Bool

/-- Forgiving the offender and discharging the claimant differ in this toy domain. -/
theorem mercy_alone_does_not_settle_every_claim :
    ¬ (∀ s : MoralRecord, s.forgiven = true → s.victimClaimSettled = true) := by
  intro h
  have contra : false = true := h ⟨true, false⟩ rfl
  cases contra

/-- This is an explicit policy *chosen* to include a capacity condition. -/
def ToyAccountable (capable culpable : Bool) : Bool := capable && culpable

theorem toy_accountability_requires_capacity (culpable : Bool) :
    ToyAccountable false culpable = false := by
  cases culpable <;> rfl

/-- A classifier of morally sufficient features is invariant within its fibers. -/
theorem same_features_same_output {X : Type u} {Feature : Type v} {Verdict : Type w}
    (features : X → Feature) (f : Feature → Verdict)
    (x y : X) (h : features x = features y) :
    f (features x) = f (features y) := congrArg f h

end DivineElegance
