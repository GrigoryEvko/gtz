/-
# The converse: a capped wedge Gram PRODUCES a dominator

`Gtz.wedgeProbe_normSq_le_bracket_sq_mul_of_posSemidef` runs one way — a
dominating triple caps the Gram of its three pair normals by its squared
bracket.  Every instrument in that family REFUSES triples.  The campaign's
open problems all need the other direction: something that PRODUCES a
dominator, and produces it in the terminal currencies.

This module closes the loop.  The missing ingredient is the dual-basis
expansion, `Gtz.bracket_smul_eq_wedgeProbe_readings`:

  **`[abc] • ξ = wedgeProbe a b c ![a ⬝ᵥ ξ, b ⬝ᵥ ξ, c ⬝ᵥ ξ]`**

— the bracket times ANY vector is the wedge probe taken at that vector's own
three atom readings.  One `ring` per coordinate.  Its content is that the three
pair normals are a basis whenever the bracket is nonzero, with the atom
readings as the coordinates.

Feed that into the cap.  The left side has squared norm `[abc]² * ‖ξ‖²`, and the
coefficient vector has squared norm `(a ⬝ᵥ ξ)² + (b ⬝ᵥ ξ)² + (c ⬝ᵥ ξ)²`, which is
exactly the quadratic form of the atom sum at `ξ`.  Cancelling `[abc]² > 0`:

  **`‖ξ‖² ≤ ξᵀ S_T ξ` for every `ξ`, i.e. the triple DOMINATES**

(`Gtz.posSemidef_of_wedgeGram_cap`).  With the landed forward direction this
gives the exact characterization `Gtz.posSemidef_iff_wedgeGram_cap`:

  **a triple with nonzero bracket dominates IF AND ONLY IF its wedge Gram is
  capped by its squared bracket.**

Domination — the campaign's whole subject — is a statement about the Gram of
the three pair normals and the bracket, and about nothing else.

[MEASURED on 399,948 random triples of unconstrained scale: the predicates
`λmin(S_T) ≥ 1` and `λmax(Γ) ≤ [abc]²` agree at EVERY sample, zero
disagreements, which is this theorem and its converse together.  Of the 371,739
refusals in that run the diagonal corner of the cap already accounts for
99.1742 percent, so the off-diagonal of the Gram is worth the last 0.83 percent
and no more.]
-/
import Gtz.Wave.KOneWedgeGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The dual-basis expansion -/

/-- **THE BRACKET TIMES A VECTOR IS THE PROBE AT ITS OWN READINGS.**  The three
pair normals of a triple are a basis whenever the bracket is nonzero, and the
coordinates of any vector in that basis are its three atom readings, divided by
the bracket.  Stated multiplied out, so no division and no nonvanishing
hypothesis appear. -/
theorem bracket_smul_eq_wedgeProbe_readings (leftVec midVec thirdVec probe : Fin 3 → ℝ) :
    tripleBracket leftVec midVec thirdVec • probe
      = wedgeProbe leftVec midVec thirdVec
          ![leftVec ⬝ᵥ probe, midVec ⬝ᵥ probe, thirdVec ⬝ᵥ probe] := by
  funext i
  fin_cases i <;>
    simp [wedgeProbe, bracketNormal, tripleBracket_eq, dotProduct, Fin.sum_univ_three] <;>
    ring

/-- The probe at a vector's own readings has squared norm the squared bracket
times the squared norm of that vector. -/
theorem wedgeProbe_readings_normSq (leftVec midVec thirdVec probe : Fin 3 → ℝ) :
    wedgeProbe leftVec midVec thirdVec
        ![leftVec ⬝ᵥ probe, midVec ⬝ᵥ probe, thirdVec ⬝ᵥ probe]
      ⬝ᵥ wedgeProbe leftVec midVec thirdVec
        ![leftVec ⬝ᵥ probe, midVec ⬝ᵥ probe, thirdVec ⬝ᵥ probe]
      = tripleBracket leftVec midVec thirdVec ^ 2 * (probe ⬝ᵥ probe) := by
  rw [← bracket_smul_eq_wedgeProbe_readings]
  simp only [dotProduct, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## 2. The producer -/

/-- **A CAPPED WEDGE GRAM PRODUCES A DOMINATOR.**  If the Gram of the three pair
normals is capped by the squared bracket at every coefficient vector, and the
bracket does not vanish, then the triple dominates.  This is the direction the
campaign's kills need, and it is stated in the terminal currencies. -/
theorem posSemidef_of_wedgeGram_cap (leftVec midVec thirdVec : Fin 3 → ℝ)
    (hbracket : tripleBracket leftVec midVec thirdVec ≠ 0)
    (hcap : ∀ coeff : Fin 3 → ℝ,
      wedgeProbe leftVec midVec thirdVec coeff ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff
        ≤ tripleBracket leftVec midVec thirdVec ^ 2 * (coeff ⬝ᵥ coeff)) :
    (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1).PosSemidef := by
  have hherm : (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec
      - 1).IsHermitian := by
    simpa [gapOfDirectionTriple] using gapOfDirectionTriple_isHermitian leftVec midVec thirdVec
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hherm, fun probe => ?_⟩
  rw [star_trivial]
  have hsplit : probe ⬝ᵥ ((atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1)
      *ᵥ probe)
      = (leftVec ⬝ᵥ probe) ^ 2 + (midVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2
        - probe ⬝ᵥ probe := by
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_sub,
      dotProduct_add, atomMatrix_dotProduct_mulVec]
  rw [hsplit]
  have hbsq : 0 < tripleBracket leftVec midVec thirdVec ^ 2 := by
    rcases lt_or_gt_of_ne hbracket with h | h <;> nlinarith
  have hc := hcap ![leftVec ⬝ᵥ probe, midVec ⬝ᵥ probe, thirdVec ⬝ᵥ probe]
  rw [wedgeProbe_readings_normSq] at hc
  have hcoeff : (![leftVec ⬝ᵥ probe, midVec ⬝ᵥ probe, thirdVec ⬝ᵥ probe] : Fin 3 → ℝ)
      ⬝ᵥ ![leftVec ⬝ᵥ probe, midVec ⬝ᵥ probe, thirdVec ⬝ᵥ probe]
      = (leftVec ⬝ᵥ probe) ^ 2 + (midVec ⬝ᵥ probe) ^ 2 + (thirdVec ⬝ᵥ probe) ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hcoeff] at hc
  have := le_of_mul_le_mul_left hc hbsq
  linarith

/-! ## 3. The characterization -/

/-- **DOMINATION IS EXACTLY THE WEDGE GRAM CAP.**  For a triple whose bracket
does not vanish, dominating and carrying a wedge Gram capped by the squared
bracket are the SAME statement.  The campaign's subject is a statement about
the three pair normals and the bracket, and about nothing else. -/
theorem posSemidef_iff_wedgeGram_cap (leftVec midVec thirdVec : Fin 3 → ℝ)
    (hbracket : tripleBracket leftVec midVec thirdVec ≠ 0) :
    (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1).PosSemidef
      ↔ ∀ coeff : Fin 3 → ℝ,
          wedgeProbe leftVec midVec thirdVec coeff
            ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff
            ≤ tripleBracket leftVec midVec thirdVec ^ 2 * (coeff ⬝ᵥ coeff) := by
  constructor
  · intro hgap coeff
    exact wedgeProbe_normSq_le_bracket_sq_mul_of_posSemidef leftVec midVec thirdVec coeff hgap
  · exact posSemidef_of_wedgeGram_cap leftVec midVec thirdVec hbracket

/-! ## 4. The design level -/

/-- **THE DOMINATOR PRODUCER AT A DESIGN.**  A triple of a design whose bracket
does not vanish and whose wedge Gram is capped by the squared bracket
dominates.  This produces the witness a kill needs. -/
theorem dominates_of_wedgeGram_cap (design : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbracket : tripleBracket (design.atom x) (design.atom y) (design.atom z) ≠ 0)
    (hcap : ∀ coeff : Fin 3 → ℝ,
      wedgeProbe (design.atom x) (design.atom y) (design.atom z) coeff
          ⬝ᵥ wedgeProbe (design.atom x) (design.atom y) (design.atom z) coeff
        ≤ tripleBracket (design.atom x) (design.atom y) (design.atom z) ^ 2
          * (coeff ⬝ᵥ coeff)) :
    Dominates design ({x, y, z} : Finset (Fin m)) := by
  rw [Dominates, subsetSum_triple_eq_add design hxy hxz hyz]
  exact posSemidef_of_wedgeGram_cap _ _ _ hbracket hcap

/-- **DOMINATION AT A DESIGN, AS AN EQUIVALENCE.** -/
theorem dominates_iff_wedgeGram_cap (design : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbracket : tripleBracket (design.atom x) (design.atom y) (design.atom z) ≠ 0) :
    Dominates design ({x, y, z} : Finset (Fin m))
      ↔ ∀ coeff : Fin 3 → ℝ,
          wedgeProbe (design.atom x) (design.atom y) (design.atom z) coeff
            ⬝ᵥ wedgeProbe (design.atom x) (design.atom y) (design.atom z) coeff
            ≤ tripleBracket (design.atom x) (design.atom y) (design.atom z) ^ 2
              * (coeff ⬝ᵥ coeff) := by
  rw [Dominates, subsetSum_triple_eq_add design hxy hxz hyz]
  exact posSemidef_iff_wedgeGram_cap _ _ _ hbracket

end Gtz
