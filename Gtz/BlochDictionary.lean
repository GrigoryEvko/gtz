/-
# The g-space dictionary: Bloch squares and concrete planar silence

Connects the abstract planar platform (`PlanarPlatform.lean`) to actual
families of planar 2-vectors, completing Corollary R″ end-to-end:

* `blochSquare` — the double-angle (Bloch) square of a planar atom: the
  traceless part of `g gᵀ` in `(cos 2θ, sin 2θ)` coordinates, with
  `⟨S(g), S(h)⟩ = 2⟨g,h⟩² − |g|²|h|²` and `|S(g)| = |g|²` — so the
  shifted-leverage parameters `z_c = ℓ_c − 2a` make `pairEntry` equal the
  gatecap obstruction `2[p_cd² − (ℓ_c−a)(ℓ_d−a)]` exactly;
* `pairEntry_bloch_nonneg_of_silent` — the concrete silence step: a pair that
  is heavy at level `a` and does NOT dominate at level `a` has nonnegative
  pair entry (2×2 trace/determinant decoding via `posSemidef_two_iff`);
* `posSemidef_planarMaster_bloch_of_silent` — **Corollary R″, concrete form**:
  on any silent heavy subfamily the Bloch master matrix is PSD, residuals
  included, no design hypothesis.
-/
import Mathlib
import Gtz.Basic
import Gtz.TwoByTwo
import Gtz.PlanarPlatform

namespace Gtz

open Matrix

variable {m : ℕ}

/-- The planar double-angle (Bloch) square of a 2-vector. -/
def blochSquare (planarAtom : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![planarAtom 0 ^ 2 - planarAtom 1 ^ 2, 2 * planarAtom 0 * planarAtom 1]

/-- The Bloch pairing: `⟨S(g), S(h)⟩ = 2⟨g,h⟩² − |g|²|h|²`. -/
theorem blochSquare_dotProduct (leftAtom rightAtom : Fin 2 → ℝ) :
    blochSquare leftAtom ⬝ᵥ blochSquare rightAtom
      = 2 * (leftAtom ⬝ᵥ rightAtom) ^ 2
        - (leftAtom ⬝ᵥ leftAtom) * (rightAtom ⬝ᵥ rightAtom) := by
  simp only [blochSquare, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The Bloch square has norm-squared `|g|⁴`: its length IS the leverage. -/
theorem blochSquare_normSq (planarAtom : Fin 2 → ℝ) :
    blochSquare planarAtom ⬝ᵥ blochSquare planarAtom
      = (planarAtom ⬝ᵥ planarAtom) ^ 2 := by
  rw [blochSquare_dotProduct]
  ring

/-- Under the Bloch dictionary with `z_c = ℓ_c − 2a`, the abstract pair entry
is exactly the gatecap obstruction `2[p_cd² − (ℓ_c−a)(ℓ_d−a)]`. -/
theorem pairEntry_bloch (atoms : Fin m → Fin 2 → ℝ) (a : ℝ) (c d : Fin m) :
    pairEntry (fun e => blochSquare (atoms e))
        (fun e => atoms e ⬝ᵥ atoms e - 2 * a) a c d
      = 2 * ((atoms c ⬝ᵥ atoms d) ^ 2
          - (atoms c ⬝ᵥ atoms c - a) * (atoms d ⬝ᵥ atoms d - a)) := by
  simp only [pairEntry, blochSquare_dotProduct]
  ring

/-- The level-shifted pair matrix is symmetric. -/
private theorem pairShift_transpose (leftAtom rightAtom : Fin 2 → ℝ)
    (a : ℝ) :
    (Matrix.vecMulVec leftAtom leftAtom
        + Matrix.vecMulVec rightAtom rightAtom
        - a • (1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ
      = Matrix.vecMulVec leftAtom leftAtom
        + Matrix.vecMulVec rightAtom rightAtom
        - a • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.transpose_vecMulVec,
    Matrix.transpose_vecMulVec]

/-- **The concrete silence step of Corollary R″**: a pair heavy at level `a`
that does not dominate at level `a` has nonnegative pair entry. -/
theorem pairEntry_bloch_nonneg_of_silent (atoms : Fin m → Fin 2 → ℝ)
    (a : ℝ) (c d : Fin m)
    (hheavyC : a ≤ atoms c ⬝ᵥ atoms c) (hheavyD : a ≤ atoms d ⬝ᵥ atoms d)
    (hsilent : ¬ (Matrix.vecMulVec (atoms c) (atoms c)
        + Matrix.vecMulVec (atoms d) (atoms d)
        - a • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef) :
    0 ≤ pairEntry (fun e => blochSquare (atoms e))
        (fun e => atoms e ⬝ᵥ atoms e - 2 * a) a c d := by
  rw [pairEntry_bloch]
  set pairShift := Matrix.vecMulVec (atoms c) (atoms c)
    + Matrix.vecMulVec (atoms d) (atoms d)
    - a • (1 : Matrix (Fin 2) (Fin 2) ℝ) with hpairShift
  have hentry00 : pairShift 0 0 = atoms c 0 ^ 2 + atoms d 0 ^ 2 - a := by
    simp [hpairShift, Matrix.vecMulVec_apply]
    ring
  have hentry11 : pairShift 1 1 = atoms c 1 ^ 2 + atoms d 1 ^ 2 - a := by
    simp [hpairShift, Matrix.vecMulVec_apply]
    ring
  have hentry01 : pairShift 0 1 = atoms c 0 * atoms c 1
      + atoms d 0 * atoms d 1 := by
    simp [hpairShift, Matrix.vecMulVec_apply]
  have hdotC : atoms c ⬝ᵥ atoms c = atoms c 0 ^ 2 + atoms c 1 ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_two]
    ring
  have hdotD : atoms d ⬝ᵥ atoms d = atoms d 0 ^ 2 + atoms d 1 ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_two]
    ring
  have hdotCD : atoms c ⬝ᵥ atoms d = atoms c 0 * atoms d 0
      + atoms c 1 * atoms d 1 := by
    simp only [dotProduct, Fin.sum_univ_two]
  rcases eq_or_lt_of_le
      (add_nonneg (sub_nonneg.mpr hheavyC) (sub_nonneg.mpr hheavyD)) with
    htr0 | htrpos
  · -- Zero trace: both leverages sit exactly at the level; the entry is a
    -- pure square.
    have hlevC : atoms c ⬝ᵥ atoms c - a = 0 := by linarith
    have hlevD : atoms d ⬝ᵥ atoms d - a = 0 := by linarith
    rw [hlevC, hlevD]
    nlinarith [sq_nonneg (atoms c ⬝ᵥ atoms d)]
  · -- Positive trace: silence decodes to a negative determinant.
    have htrace : 0 < pairShift 0 0 + pairShift 1 1 := by
      rw [hentry00, hentry11]
      have := htrpos
      rw [hdotC, hdotD] at this
      linarith
    have hdet : ¬ (0 ≤ pairShift 0 0 * pairShift 1 1 - pairShift 0 1 ^ 2) :=
      fun hcontra => hsilent
        ((posSemidef_two_iff_of_trace_pos
          (pairShift_transpose (atoms c) (atoms d) a) htrace).mpr hcontra)
    push Not at hdet
    have hdetform : pairShift 0 0 * pairShift 1 1 - pairShift 0 1 ^ 2
        = (atoms c ⬝ᵥ atoms c - a) * (atoms d ⬝ᵥ atoms d - a)
          - (atoms c ⬝ᵥ atoms d) ^ 2 := by
      rw [hentry00, hentry11, hentry01, hdotC, hdotD, hdotCD]
      ring
    rw [hdetform] at hdet
    linarith

/-- **Corollary R″, concrete planar form, end-to-end**: for any family of
planar atoms, any subfamily `E` heavy at level `a` with no `E`-pair dominating
at level `a` is silent, and the Bloch master matrix over `E` is PSD — with the
closure/trace/weight residuals present and NO design hypothesis. -/
theorem posSemidef_planarMaster_bloch_of_silent (E : Finset (Fin m))
    (atoms : Fin m → Fin 2 → ℝ) (weight : Fin m → ℝ) (a : ℝ)
    (hweight : ∀ c ∈ E, 0 ≤ weight c)
    (hheavy : ∀ c ∈ E, a ≤ atoms c ⬝ᵥ atoms c)
    (hsilent : ∀ c ∈ E, ∀ d ∈ E, c ≠ d →
      ¬ (Matrix.vecMulVec (atoms c) (atoms c)
          + Matrix.vecMulVec (atoms d) (atoms d)
          - a • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef) :
    (planarMaster E (fun e => blochSquare (atoms e)) weight
        (fun e => atoms e ⬝ᵥ atoms e - 2 * a) a).PosSemidef :=
  posSemidef_planarMaster_of_pairEntry_nonneg E _ weight _ a hweight
    fun c hc d hd hne => pairEntry_bloch_nonneg_of_silent atoms a c d
      (hheavy c hc) (hheavy d hd) (hsilent c hc d hd hne)

end Gtz
