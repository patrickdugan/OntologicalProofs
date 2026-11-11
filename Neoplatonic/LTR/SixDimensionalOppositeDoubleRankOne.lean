import Neoplatonic.LTR.SixDimensionalSignedCornerRankTwo
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-!
# LTR-MAN-95: a two-dimensional saturated corner is rank one

The next step after MAN-94's genuine rank-two corner theorem is an
independent, exact 2x2 algebraic lemma.

If T Tᴴ is idempotent with trace one, then T has complex rank one
and determinant zero. Applied to T = 2i B, this is precisely the
rank-one/single-singular-value certificate for the surviving
opposite-double Dirac block. The full six-dimensional-to-two-dimensional
block-identification lemma remains a separate bridge.
-/

namespace Neoplatonic.LTR

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A complex 2x2 idempotent has trace equal to its matrix rank. -/
theorem twoMatrix_idempotent_trace_eq_rank
    (P : TwoMat) (hP : P * P = P) :
    P.trace = (P.rank : ℂ) := by
  let e : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := P.toLin'
  have he : IsIdempotentElem e := by
    change e ∘ₗ e = e
    simpa only [e, Matrix.toLin'_mul] using congrArg Matrix.toLin' hP
  have htr := (LinearMap.IsIdempotentElem.isProj_range e he).trace
  change LinearMap.trace ℂ (Fin 2 → ℂ) e =
    (Module.finrank ℂ (LinearMap.range e) : ℂ) at htr
  dsimp only [e] at htr
  rw [Matrix.trace_toLin'_eq] at htr
  change P.trace = (P.rank : ℂ) at htr
  exact htr

/-- A 2x2 idempotent of trace one has zero determinant.
The proof expands the two diagonal entries of P²=P and uses
the 2x2 determinant formula; no diagonalization is assumed. -/
theorem twoMatrix_idempotent_traceOne_det_zero
    (P : TwoMat) (hP : P * P = P) (htrace : P.trace = 1) :
    P.det = 0 := by
  have h00 : P 0 0 * P 0 0 + P 0 1 * P 1 0 = P 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : TwoMat => M 0 0) hP
  have h11 : P 1 0 * P 0 1 + P 1 1 * P 1 1 = P 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : TwoMat => M 1 1) hP
  have ht : P 0 0 + P 1 1 = (1 : ℂ) := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using htrace
  have htwice :
      (2 : ℂ) * (P 0 0 * P 1 1 - P 0 1 * P 1 0) = 0 := by
    calc
      (2 : ℂ) * (P 0 0 * P 1 1 - P 0 1 * P 1 0) =
          (P 0 0 + P 1 1) * (P 0 0 + P 1 1) -
            ((P 0 0 * P 0 0 + P 0 1 * P 1 0) +
             (P 1 0 * P 0 1 + P 1 1 * P 1 1)) := by ring
      _ = 1 - (P 0 0 + P 1 1) := by rw [h00, h11, ht]; ring
      _ = 0 := by rw [ht]; ring
  have hdet : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 0 :=
    (mul_eq_zero.mp htwice).resolve_left (by norm_num)
  simpa only [Matrix.det_fin_two] using hdet

/-- A scaled 2x2 partial-isometry block has rank one and zero determinant
when its final projection has trace one. The scale may be any
nonzero complex number. -/
theorem twoMatrix_scaledPartialIsometry_traceOne_rankOne
    (B : TwoMat) (s : ℂ) (hs : s ≠ 0)
    (hproj :
      let T : TwoMat := s • B
      (T * T.conjTranspose) * (T * T.conjTranspose) =
        T * T.conjTranspose)
    (htrace :
      let T : TwoMat := s • B
      (T * T.conjTranspose).trace = 1) :
    B.rank = 1 ∧ B.det = 0 := by
  let T : TwoMat := s • B
  change (T * T.conjTranspose) * (T * T.conjTranspose) =
    T * T.conjTranspose at hproj
  change (T * T.conjTranspose).trace = 1 at htrace
  have hPrank : (T * T.conjTranspose).rank = 1 := by
    have h := twoMatrix_idempotent_trace_eq_rank
      (T * T.conjTranspose) hproj
    rw [htrace] at h
    exact_mod_cast h.symm
  have hPdet : (T * T.conjTranspose).det = 0 :=
    twoMatrix_idempotent_traceOne_det_zero
      (T * T.conjTranspose) hproj htrace
  have hTdet : T.det = 0 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose] at hPdet
    rcases mul_eq_zero.mp hPdet with h | h
    · exact h
    · have h' := congrArg star h
      simpa using h'
  have hTle : T.rank ≤ 1 := by
    by_contra hle
    have hmax : T.rank ≤ 2 := Matrix.rank_le_width T
    have hfull : T.rank = 2 := by omega
    have hsurj : Function.Surjective T.mulVec :=
      Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by
        simpa only [Fintype.card_fin] using hfull)
    have hunit : IsUnit T := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
    have hdet_ne : T.det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det T).mp hunit).ne_zero
    exact hdet_ne hTdet
  have hTge : 1 ≤ T.rank := by
    have hle : (T * T.conjTranspose).rank ≤ T.rank :=
      Matrix.rank_mul_le_left T T.conjTranspose
    omega
  have hTrank : T.rank = 1 := by omega
  have hBrank : B.rank = 1 := by
    have hr : T.rank = B.rank := by
      change (s • B).rank = B.rank
      exact Matrix.rank_smul_of_mem_nonZeroDivisors B
        (mem_nonZeroDivisors_of_ne_zero hs)
    exact hr.symm.trans hTrank
  have hBdet : B.det = 0 := by
    change (s • B).det = 0 at hTdet
    rw [Matrix.det_smul] at hTdet
    have h : s ^ 2 * B.det = 0 := by
      simpa only [Fintype.card_fin] using hTdet
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 hs)
  exact ⟨hBrank, hBdet⟩

/-- The exact coefficient 2i of the surviving Hamming opposite
corner is nonzero, so the general theorem applies without a
separate nonvanishing hypothesis. -/
theorem twoMatrix_doubleImagPartialIsometry_traceOne_rankOne
    (B : TwoMat)
    (hproj :
      let T : TwoMat := ((2 : ℂ) * Complex.I) • B
      (T * T.conjTranspose) * (T * T.conjTranspose) =
        T * T.conjTranspose)
    (htrace :
      let T : TwoMat := ((2 : ℂ) * Complex.I) • B
      (T * T.conjTranspose).trace = 1) :
    B.rank = 1 ∧ B.det = 0 := by
  exact twoMatrix_scaledPartialIsometry_traceOne_rankOne
    B ((2 : ℂ) * Complex.I) (by norm_num) hproj htrace

/-! ## Abstract four-dimensional opposite-corner tripotence -/

private abbrev FourMat :=
  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ

/-- The surviving four-dimensional opposite-double corner, written
as the off-diagonal Hermitian block matrix of the scaled 2x2 map. -/
def twoFibreOppositeCorner (T : TwoMat) : FourMat :=
  Matrix.fromBlocks 0 T T.conjTranspose 0

/-- The MAN-93 tripotence identity of an off-diagonal Hermitian
four-corner immediately makes T Tᴴ idempotent. -/
theorem twoFibreOppositeCorner_tripotent_projection
    (T : TwoMat)
    (htrip : twoFibreOppositeCorner T *
        twoFibreOppositeCorner T *
        twoFibreOppositeCorner T =
          twoFibreOppositeCorner T) :
    (T * T.conjTranspose) * (T * T.conjTranspose) =
      T * T.conjTranspose := by
  let K : FourMat := twoFibreOppositeCorner T
  have hKsq :
      K * K = Matrix.fromBlocks (T * T.conjTranspose)
        (0 : TwoMat) 0 (T.conjTranspose * T) := by
    dsimp [K, twoFibreOppositeCorner]
    rw [Matrix.fromBlocks_multiply]
    simp
  have hKcube :
      K * K * K =
        Matrix.fromBlocks (0 : TwoMat)
          ((T * T.conjTranspose) * T)
          ((T.conjTranspose * T) * T.conjTranspose)
          (0 : TwoMat) := by
    rw [hKsq]
    dsimp [K, twoFibreOppositeCorner]
    rw [Matrix.fromBlocks_multiply]
    simp
  have hTTT : (T * T.conjTranspose) * T = T := by
    have h := congrArg (fun M : FourMat => M.toBlocks₁₂) htrip
    change (K * K * K).toBlocks₁₂ = K.toBlocks₁₂ at h
    rw [hKcube] at h
    simpa [K, twoFibreOppositeCorner] using h
  calc
    (T * T.conjTranspose) * (T * T.conjTranspose) =
        ((T * T.conjTranspose) * T) * T.conjTranspose := by noncomm_ring
    _ = T * T.conjTranspose := by rw [hTTT]

/-- Rank one follows directly from corner tripotence and its
fixed unit trace, using the two-dimensional determinant criterion. -/
theorem twoFibreOppositeCorner_tripotent_traceOne_rankOne
    (B : TwoMat) (s : ℂ) (hs : s ≠ 0)
    (htrip :
      let T : TwoMat := s • B
      twoFibreOppositeCorner T * twoFibreOppositeCorner T *
        twoFibreOppositeCorner T = twoFibreOppositeCorner T)
    (htrace :
      let T : TwoMat := s • B
      (T * T.conjTranspose).trace = 1) :
    B.rank = 1 ∧ B.det = 0 := by
  apply twoMatrix_scaledPartialIsometry_traceOne_rankOne B s hs
  · exact twoFibreOppositeCorner_tripotent_projection (s • B) htrip
  · exact htrace

/-- Specialized off-diagonal corner model for a Hermitian Hamming
witness with actual scalar coefficient 2i. -/
theorem twoFibreOppositeCorner_doubleImag_tripotent_rankOne
    (B : TwoMat)
    (htrip :
      let T : TwoMat := ((2 : ℂ) * Complex.I) • B
      twoFibreOppositeCorner T * twoFibreOppositeCorner T *
        twoFibreOppositeCorner T = twoFibreOppositeCorner T)
    (htrace :
      let T : TwoMat := ((2 : ℂ) * Complex.I) • B
      (T * T.conjTranspose).trace = 1) :
    B.rank = 1 ∧ B.det = 0 := by
  exact twoFibreOppositeCorner_tripotent_traceOne_rankOne
    B ((2 : ℂ) * Complex.I) (by norm_num) htrip htrace

/-! ## Square-trace bridge: the MAN-94 numerical invariant -/

/-- Trace of the diagonal two-by-two blocks in the canonical
four-dimensional direct-sum chart. -/
theorem fourMatrix_diagonalBlock_trace
    (A B : TwoMat) :
    (Matrix.fromBlocks A 0 0 B : FourMat).trace = A.trace + B.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks]

/-- The square of the opposite-double Hermitian corner has
twice the trace of the positive two-dimensional Gram matrix. -/
theorem twoFibreOppositeCorner_square_trace (T : TwoMat) :
    (twoFibreOppositeCorner T * twoFibreOppositeCorner T).trace =
      (2 : ℂ) * (T * T.conjTranspose).trace := by
  have hsq : twoFibreOppositeCorner T * twoFibreOppositeCorner T =
      Matrix.fromBlocks (T * T.conjTranspose)
        (0 : TwoMat) 0 (T.conjTranspose * T) := by
    unfold twoFibreOppositeCorner
    rw [Matrix.fromBlocks_multiply]
    simp
  rw [hsq, fourMatrix_diagonalBlock_trace]
  have hcyc : (T.conjTranspose * T).trace =
      (T * T.conjTranspose).trace :=
    Matrix.trace_mul_comm T.conjTranspose T
  rw [hcyc]
  ring

/-- A tripotent four-dimensional opposite corner of square-trace
two has rank-one off-diagonal 2x2 block and zero determinant.
This is the exact spectral consequence needed after transporting
MAN-94 from the six-coordinate Dirac chart. -/
theorem twoFibreOppositeCorner_tripotent_squareTraceTwo_rankOne
    (B : TwoMat) (s : ℂ) (hs : s ≠ 0)
    (htrip :
      let T : TwoMat := s • B
      twoFibreOppositeCorner T * twoFibreOppositeCorner T *
        twoFibreOppositeCorner T = twoFibreOppositeCorner T)
    (htrace2 :
      let T : TwoMat := s • B
      (twoFibreOppositeCorner T * twoFibreOppositeCorner T).trace = 2) :
    B.rank = 1 ∧ B.det = 0 := by
  apply twoFibreOppositeCorner_tripotent_traceOne_rankOne B s hs htrip
  have ht := twoFibreOppositeCorner_square_trace (s • B)
  change (twoFibreOppositeCorner (s • B) *
      twoFibreOppositeCorner (s • B)).trace = 2 at htrace2
  rw [htrace2] at ht
  linear_combination (-1 / 2 : ℂ) * ht

/-- The 2i-scaled opposite-double corner is rank one as soon as
its intrinsic tripotence and square-trace-two properties hold. -/
theorem twoFibreOppositeCorner_doubleImag_squareTraceTwo_rankOne
    (B : TwoMat)
    (htrip :
      let T : TwoMat := ((2 : ℂ) * Complex.I) • B
      twoFibreOppositeCorner T * twoFibreOppositeCorner T *
        twoFibreOppositeCorner T = twoFibreOppositeCorner T)
    (htrace2 :
      let T : TwoMat := ((2 : ℂ) * Complex.I) • B
      (twoFibreOppositeCorner T * twoFibreOppositeCorner T).trace = 2) :
    B.rank = 1 ∧ B.det = 0 := by
  exact twoFibreOppositeCorner_tripotent_squareTraceTwo_rankOne
    B ((2 : ℂ) * Complex.I) (by norm_num) htrip htrace2

/-! ## Full six-dimensional bipartite rank certificate -/

/-- In the actual six-dimensional algebra, a rank-one conclusion
follows directly from a bipartite tripotent and its square trace.
The matrix B is allowed to be six-by-six, with its nonzero entries
supported on a proper rectangular truth-fibre block. -/
theorem sixMatrix_bipartite_partialIsometry_rankOne
    (B Z : SixMat)
    (hBB : B * B = 0)
    (hZZ : Z * Z = 0)
    (hBZB : B * Z * B = B)
    (htrace : ((B + Z) * (B + Z)).trace = (2 : ℂ)) :
    B.rank = 1 := by
  have hSq : (B + Z) * (B + Z) = B * Z + Z * B := by
    calc
      (B + Z) * (B + Z) =
          B * B + B * Z + Z * B + Z * Z := by noncomm_ring
      _ = B * Z + Z * B := by rw [hBB, hZZ]; simp
  have hsum : (B * Z).trace + (Z * B).trace = (2 : ℂ) := by
    have h := congrArg Matrix.trace hSq
    rw [Matrix.trace_add] at h
    rw [htrace] at h
    exact h.symm
  have hcyc := Matrix.trace_mul_comm B Z
  rw [← hcyc] at hsum
  have hBZtrace : (B * Z).trace = (1 : ℂ) := by
    linear_combination (1 / 2 : ℂ) * hsum
  have hProj : (B * Z) * (B * Z) = B * Z := by
    calc
      (B * Z) * (B * Z) = (B * Z * B) * Z := by noncomm_ring
      _ = B * Z := by rw [hBZB]
  have hRankBZ : (B * Z).rank = 1 := by
    have h := sixMatrix_idempotent_trace_eq_rank (B * Z) hProj
    rw [hBZtrace] at h
    exact_mod_cast h.symm
  have hle : B.rank ≤ (B * Z).rank := by
    calc
      B.rank = (B * Z * B).rank := congrArg Matrix.rank hBZB.symm
      _ ≤ (B * Z).rank := Matrix.rank_mul_le_left (B * Z) B
  have hge : (B * Z).rank ≤ B.rank :=
    Matrix.rank_mul_le_left B Z
  omega

/-- A pair of square-zero off-diagonal blocks is individually
tripotent in the required sense whenever the total corner is
tripotent and the two sectors have disjoint left/right supports. -/
theorem sixMatrix_bipartite_tripotent_extract
    (B Z P R : SixMat)
    (hBB : B * B = 0)
    (hZZ : Z * Z = 0)
    (hPB : P * B = B)
    (hBR : B * R = B)
    (hPZ : P * Z = 0)
    (hZR : Z * R = 0)
    (htrip :
      (B + Z) * (B + Z) * (B + Z) = B + Z) :
    B * Z * B = B := by
  have hSq : (B + Z) * (B + Z) = B * Z + Z * B := by
    calc
      (B + Z) * (B + Z) =
          B * B + B * Z + Z * B + Z * Z := by noncomm_ring
      _ = B * Z + Z * B := by rw [hBB, hZZ]; simp
  have hCube :
      (B + Z) * (B + Z) * (B + Z) =
        B * Z * B + Z * B * Z := by
    rw [hSq]
    calc
      (B * Z + Z * B) * (B + Z) =
          B * Z * B + B * (Z * Z) +
            Z * (B * B) + Z * B * Z := by noncomm_ring
      _ = B * Z * B + Z * B * Z := by rw [hBB, hZZ]; simp
  have hL : P * (B * Z * B) * R = B * Z * B := by
    calc
      P * (B * Z * B) * R = (P * B) * Z * (B * R) := by noncomm_ring
      _ = B * Z * B := by rw [hPB, hBR]
  have hZ : P * (Z * B * Z) * R = 0 := by
    calc
      P * (Z * B * Z) * R = (P * Z) * B * (Z * R) := by noncomm_ring
      _ = 0 := by rw [hPZ, hZR]; simp
  have hR : P * (B + Z) * R = B := by
    calc
      P * (B + Z) * R = P * B * R + P * Z * R := by noncomm_ring
      _ = B := by rw [hPB, hBR, hPZ]; simp
  have hSum :
      P * (B * Z * B + Z * B * Z) * R = B * Z * B := by
    calc
      _ = P * (B * Z * B) * R + P * (Z * B * Z) * R := by
        noncomm_ring
      _ = B * Z * B := by rw [hL, hZ]; simp
  calc
    B * Z * B = P * (B * Z * B + Z * B * Z) * R := hSum.symm
    _ = P * ((B + Z) * (B + Z) * (B + Z)) * R := by rw [hCube]
    _ = P * (B + Z) * R := by rw [htrip]
    _ = B := hR

/-- The complete six-dimensional rank-one theorem, with
precise bipartite support assumptions kept explicit.
This avoids any complex-star ordered-field rank lemmas. -/
theorem sixMatrix_bipartite_tripotent_traceTwo_rankOne
    (B Z P R : SixMat)
    (hBB : B * B = 0)
    (hZZ : Z * Z = 0)
    (hPB : P * B = B)
    (hBR : B * R = B)
    (hPZ : P * Z = 0)
    (hZR : Z * R = 0)
    (htrip :
      (B + Z) * (B + Z) * (B + Z) = B + Z)
    (htrace : ((B + Z) * (B + Z)).trace = (2 : ℂ)) :
    B.rank = 1 :=
  sixMatrix_bipartite_partialIsometry_rankOne B Z hBB hZZ
    (sixMatrix_bipartite_tripotent_extract
      B Z P R hBB hZZ hPB hBR hPZ hZR htrip)
    htrace

end Neoplatonic.LTR
