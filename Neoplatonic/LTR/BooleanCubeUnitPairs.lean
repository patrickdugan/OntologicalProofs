import Neoplatonic.LTR.BooleanCubeHamming

/-!
# LTR-MAN-09E: unit Hamming steps are exactly the cube Dirac edges

An arbitrary pair of Boolean assignments at Hamming distance one
is represented by exactly one lower-to-upper finite Dirac edge,
up to reversing its orientation.

Consequently the norm-one ball of the genuine global commutator
is exactly the set of functions whose complex differences have
norm at most one across all Hamming-one pairs.

This bridges the formally verified Hamming repair theorem with the
operator-theoretic edge-gradient identity.
-/

namespace Neoplatonic.LTR

/-- Any two assignments of Hamming distance one are the two
endpoints of one of the selected unoriented hypercube edges. -/
theorem booleanCube_unit_pair_is_edge {m : ℕ}
    (u v : BooleanCubeVertex m)
    (h : hammingDist u v = 1) :
    ∃ e : BooleanCubeEdge m,
      (booleanCubeEdgeLower e = u ∧ booleanCubeEdgeUpper e = v) ∨
      (booleanCubeEdgeLower e = v ∧ booleanCubeEdgeUpper e = u) := by
  classical
  let s : Finset (Fin m) :=
    Finset.univ.filter (fun i => u i ≠ v i)
  have hs : s.card = 1 := h
  obtain ⟨i, hiSet⟩ := Finset.card_eq_one.mp hs
  have hi : u i ≠ v i := by
    have himem : i ∈ s := by rw [hiSet]; simp
    exact (Finset.mem_filter.mp himem).2
  have hrest (j : Fin m) (hj : j ≠ i) : u j = v j := by
    by_contra hn
    have hjmem : j ∈ s := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
    rw [hiSet] at hjmem
    exact hj (Finset.mem_singleton.mp hjmem)
  cases hu : u i <;> cases hv : v i
  ·
      exact False.elim (hi (by simp [hu, hv]))
  ·
      have htarget : Function.update u i true = v := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [hv]
        · simpa [hj] using hrest j hj
      refine ⟨⟨i, ⟨u, hu⟩⟩, Or.inl ⟨rfl, ?_⟩⟩
      exact htarget
  ·
      have htarget : Function.update v i true = u := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [hu]
        · simpa [hj] using (hrest j hj).symm
      refine ⟨⟨i, ⟨v, hv⟩⟩, Or.inr ⟨rfl, ?_⟩⟩
      exact htarget
  ·
      exact False.elim (hi (by simp [hu, hv]))

/-- Global commutator norm at most one is equivalent to checking
the complex gradient bound on each distinct unit cube edge. -/
theorem booleanCubeCommutator_norm_one_iff_edges {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) :
    ‖booleanCubeCommutator f‖ ≤ 1 ↔
      ∀ e : BooleanCubeEdge m,
        ‖f (booleanCubeEdgeUpper e) -
          f (booleanCubeEdgeLower e)‖ ≤ 1 := by
  constructor
  · intro h e
    exact (booleanCubeLocalGradient_le_global f e).trans h
  · intro h
    have hcap : (booleanCubeGradientCap f : ℝ) ≤ 1 := by
      have hn : booleanCubeGradientCap f ≤ (1 : ℝ≥0) := by
        unfold booleanCubeGradientCap
        apply Finset.sup_le
        intro e _
        have he := h e
        rw [← booleanCubeLocalCommutator_norm] at he
        exact_mod_cast he
      exact_mod_cast hn
    exact (booleanCubeCommutator_norm_le_cap f).trans hcap

/-- The true global Dirac commutator controls every distance-one
difference, including both edge orientations. -/
theorem booleanCubeCommutator_unit_pair_bound {m : ℕ}
    (f : BooleanCubeVertex m → ℂ)
    (h : ‖booleanCubeCommutator f‖ ≤ 1)
    (u v : BooleanCubeVertex m)
    (huv : hammingDist u v = 1) :
    ‖f u - f v‖ ≤ 1 := by
  obtain ⟨e, he | he⟩ := booleanCube_unit_pair_is_edge u v huv
  · rcases he with ⟨hl, hr⟩
    have hb := (booleanCubeCommutator_norm_one_iff_edges f).mp h e
    simpa only [hl, hr, norm_sub_rev] using hb
  · rcases he with ⟨hl, hr⟩
    have hb := (booleanCubeCommutator_norm_one_iff_edges f).mp h e
    simpa only [hl, hr] using hb

/-- The operator's unit commutator ball gives the Hamming-distance
Lipschitz upper bound for arbitrary vertex pairs. -/
theorem booleanCubeCommutator_hamming_upper {m : ℕ}
    (f : BooleanCubeVertex m → ℂ)
    (h : ‖booleanCubeCommutator f‖ ≤ 1)
    (x y : BooleanCubeVertex m) :
    ‖f x - f y‖ ≤ (hammingDist x y : ℝ) := by
  exact booleanCube_unitGradients_control_hamming f
    (booleanCubeCommutator_unit_pair_bound f h) x y

end Neoplatonic.LTR
