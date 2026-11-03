import Mathlib

/-!
# Symmetry obstructs a topology-canonical metric

A metric invariant under every homeomorphism cannot coexist with arbitrarily
close distinct points and a point stabilizer transitive on the other points.
Cantor space has the needed topological homogeneity, but that specialization
and the Gödel/Rosser-to-Cantor argument are written proofs in the research note;
they are not silently treated as formalized in this module.
-/

namespace Neoplatonic.LTR

/-- Pure metric obstruction. All homogeneity and accumulation hypotheses are
explicit. This does not forbid selecting a metric after adding a filtration. -/
theorem no_homeomorphism_invariant_metric
    {X : Type*} [MetricSpace X] (x y : X) (hxy : x ≠ y)
    (close : ∀ ε : ℝ, 0 < ε → ∃ z : X, z ≠ x ∧ dist x z < ε)
    (homogeneous : ∀ z : X, z ≠ x →
      ∃ e : X ≃ₜ X, e x = x ∧ e y = z)
    (invariant : ∀ e : X ≃ₜ X, ∀ a b : X,
      dist (e a) (e b) = dist a b) : False := by
  obtain ⟨z, hzx, hz⟩ := close (dist x y) (dist_pos.mpr hxy)
  obtain ⟨e, hex, hey⟩ := homogeneous z hzx
  have hd := invariant e x y
  rw [hex, hey] at hd
  rw [hd] at hz
  exact (lt_irrefl _) hz

end Neoplatonic.LTR
