import Neoplatonic.RH
import Neoplatonic.GodelScott
import GrammyAndPrimes.SpectralSymmetry

/-!
# RH and an ontological argument: dependency audit

RiemannHypothesis here is the actual Mathlib analytic proposition, not a
boolean placeholder. God is an unspecified proposition, not a defined
or demonstrated supernatural being.

RH → God is a conditional argument. A disproof of RH yields ¬God only with a
separate bridge God → RH. Putting RH into the definition of a special
spectrally certified God makes its refutation trivial and definitional.

Finally, Scott's full axioms plus symmetry force modal collapse for any
world-varying proposition. A world-indexed report about RH is an epistemic
variable, not the mathematical truth value of RH itself.
-/

namespace GrammyAndPrimes

/-- This is just modus ponens; the mathematical hypothesis does not provide
    the bridge from zeta zeros to the existence of God. -/
theorem conditional_god_of_rh (God : Prop)
    (bridge : RiemannHypothesis → God) (rh : RiemannHypothesis) : God :=
  bridge rh

/-- The requested 'RH false ⇒ atheism' argument needs the opposite bridge. -/
theorem atheism_of_counterexample_to_rh (God : Prop)
    (bridge : God → RiemannHypothesis) (counter : ¬ RiemannHypothesis) : ¬ God :=
  fun god => counter (bridge god)

/-- A model where the forward implication holds, RH is false, and God is true.
    This rules out the tempting but invalid converse in pure propositional logic. -/
theorem false_antecedent_does_not_refute_consequent :
    ¬ (∀ R God : Prop, (R → God) → ¬ R → ¬ God) := by
  intro h
  have hnot : ¬ True := h False True (fun hf => False.elim hf) (fun hf => hf)
  exact hnot True.intro

/-- One can define a special existence claim to include RH by stipulation. -/
def SpectrallyCertifiedGod (God : Prop) : Prop := God ∧ RiemannHypothesis

/-- An RH counterexample refutes that definition, not independent God claims. -/
theorem no_spectrally_certified_god (God : Prop)
    (counter : ¬ RiemannHypothesis) : ¬ SpectrallyCertifiedGod God :=
  fun h => counter h.2

/-- Under RH, the spectral adjective adds no information. -/
theorem spectrally_certified_iff_god_under_rh (God : Prop)
    (rh : RiemannHypothesis) : SpectrallyCertifiedGod God ↔ God := by
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, rh⟩

universe u v

/-- Under Scott's premises, a separate Godlike-to-RH bridge proves RH.
    It makes that bridge, not the modal logic, the mathematical load bearer. -/
theorem rh_from_scott_with_speculative_bridge
    {W : Type u} {R : W → W → Prop} {α : Type v}
    (T : Neoplatonic.Godel.ScottTheory R α) (hsymm : Std.Symm R)
    (w : W)
    (spectralBridge : ∀ x : α,
      Neoplatonic.Godel.Godlike T.P x w → RiemannHypothesis) :
    RiemannHypothesis := by
  obtain ⟨g, hg⟩ := Neoplatonic.Godel.godlike_exists T hsymm w
  exact spectralBridge g hg

/-- Since Scott proves a Godlike inhabitant, the proposed bridge is
    logically equivalent to RH itself once Scott's assumptions are held. -/
theorem scott_spectral_bridge_iff_rh
    {W : Type u} {R : W → W → Prop} {α : Type v}
    (T : Neoplatonic.Godel.ScottTheory R α) (hsymm : Std.Symm R)
    (w : W) :
    (∀ x : α, Neoplatonic.Godel.Godlike T.P x w → RiemannHypothesis) ↔
      RiemannHypothesis := by
  constructor
  · exact rh_from_scott_with_speculative_bridge T hsymm w
  · intro rh _ _
    exact rh

/-- Scott's consistent one-world theory admits a God-like being while the
    independent toy spectrum is reflection-symmetric with off-axis points.
    This refutes a proposed *structural* implication from Scott plus setwise
    symmetry to spectral alignment. The toy is not a zeta-zero construction. -/
theorem scott_model_with_off_axis_symmetric_toy :
    ∃ T : Neoplatonic.Godel.ScottTheory (fun (_ _ : Unit) => True) Unit,
      (∃ g : Unit, Neoplatonic.Godel.Godlike T.P g ()) ∧
      (∀ b : Bool, ∃ c : Bool,
        toyCoordinate c = mirror (toyCoordinate b)) ∧
      (∃ b : Bool, toyCoordinate b ≠ (1 / 2 : ℚ)) := by
  refine ⟨Neoplatonic.Godel.trivialScott, ?_, toy_closed_under_reflection,
    toy_has_off_axis_point⟩
  exact Neoplatonic.Godel.godlike_exists Neoplatonic.Godel.trivialScott
    ⟨fun _ _ _ => trivial⟩ ()

/-- Scott's axioms propagate any proposition to an accessible world;
    by this point RH has been replaced with a world-indexed report. -/
theorem scott_propagates_rh_reports
    {W : Type u} {R : W → W → Prop} {α : Type v}
    (T : Neoplatonic.Godel.ScottTheory R α) (hsymm : Std.Symm R)
    (rhReport : W → Prop) {w v : W}
    (hwv : R w v) (hw : rhReport w) : rhReport v := by
  exact Neoplatonic.Godel.modal_collapse T hsymm w rhReport hw v hwv

/-- Therefore a frame admitting opposite reports between accessible worlds
    is incompatible with Scott's premises on a symmetric accessibility frame. -/
theorem scott_excludes_disagreeing_reports
    {W : Type u} {R : W → W → Prop} {α : Type v}
    (T : Neoplatonic.Godel.ScottTheory R α) (hsymm : Std.Symm R)
    (rhReport : W → Prop) {w v : W}
    (hwv : R w v) (hw : rhReport w) (hv : ¬ rhReport v) : False :=
  hv (scott_propagates_rh_reports T hsymm rhReport hwv hw)

/-- Concrete two-world inconsistency witness for the same modal-collapse
    phenomenon. It does not presuppose anything about the real RH. -/
theorem scott_impossible_on_total_two_world_frame :
    ¬ Nonempty (Neoplatonic.Godel.ScottTheory (fun (_ _ : Bool) => True) Unit) := by
  rintro ⟨T⟩
  have hsymm : Std.Symm (fun (_ _ : Bool) => True) :=
    ⟨fun _ _ _ => trivial⟩
  have hfalse : false = true :=
    scott_propagates_rh_reports T hsymm
      (fun b : Bool => b = true) (w := true) (v := false) trivial rfl
  cases hfalse

end GrammyAndPrimes
