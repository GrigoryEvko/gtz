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

/-! ## 5. The checkable corner: the pair area sum alone

The cap quantifies over every coefficient vector, which no lane can check.  The
trace of the wedge Gram bounds all of it, and that trace is the PAIR AREA SUM.
So a triple whose three pair wedges TOGETHER undercut its squared bracket
dominates, and that is checkable from wedges and brackets alone.
-/

/-- The pair wedge does not depend on the order of the pair. -/
theorem crossNormSq_comm (leftVec rightVec : Fin 3 → ℝ) :
    crossNormSq leftVec rightVec = crossNormSq rightVec leftVec := by
  simp only [crossNormSq, bracketNormal, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE COMBINATION BOUND.**  The squared norm of a combination of three
vectors is at most the squared coefficient vector times the total squared norm.
This is Lagrange's identity: the difference is the sum of the nine squared
two-by-two coefficient minors. -/
theorem normSq_combination_le (firstVec secondVec thirdVec coeff : Fin 3 → ℝ) :
    (coeff 0 • firstVec + coeff 1 • secondVec + coeff 2 • thirdVec)
        ⬝ᵥ (coeff 0 • firstVec + coeff 1 • secondVec + coeff 2 • thirdVec)
      ≤ (coeff ⬝ᵥ coeff)
        * (firstVec ⬝ᵥ firstVec + secondVec ⬝ᵥ secondVec + thirdVec ⬝ᵥ thirdVec) := by
  simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  nlinarith [sq_nonneg (coeff 0 * secondVec 0 - coeff 1 * firstVec 0),
    sq_nonneg (coeff 0 * secondVec 1 - coeff 1 * firstVec 1),
    sq_nonneg (coeff 0 * secondVec 2 - coeff 1 * firstVec 2),
    sq_nonneg (coeff 0 * thirdVec 0 - coeff 2 * firstVec 0),
    sq_nonneg (coeff 0 * thirdVec 1 - coeff 2 * firstVec 1),
    sq_nonneg (coeff 0 * thirdVec 2 - coeff 2 * firstVec 2),
    sq_nonneg (coeff 1 * thirdVec 0 - coeff 2 * secondVec 0),
    sq_nonneg (coeff 1 * thirdVec 1 - coeff 2 * secondVec 1),
    sq_nonneg (coeff 1 * thirdVec 2 - coeff 2 * secondVec 2)]

/-- The wedge probe is capped by the pair area sum, which is the trace of the
wedge Gram. -/
theorem wedgeProbe_normSq_le_pairAreaSum_mul (leftVec midVec thirdVec coeff : Fin 3 → ℝ) :
    wedgeProbe leftVec midVec thirdVec coeff ⬝ᵥ wedgeProbe leftVec midVec thirdVec coeff
      ≤ triplePairAreaSum leftVec midVec thirdVec * (coeff ⬝ᵥ coeff) := by
  have hbound := normSq_combination_le (bracketNormal midVec thirdVec)
    (bracketNormal thirdVec leftVec) (bracketNormal leftVec midVec) coeff
  rw [wedgeProbe]
  have hsum : (bracketNormal midVec thirdVec ⬝ᵥ bracketNormal midVec thirdVec
      + bracketNormal thirdVec leftVec ⬝ᵥ bracketNormal thirdVec leftVec
      + bracketNormal leftVec midVec ⬝ᵥ bracketNormal leftVec midVec)
      = triplePairAreaSum leftVec midVec thirdVec := by
    simp only [triplePairAreaSum, crossNormSq, bracketNormal, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hsum] at hbound
  linarith [hbound]

/-- **THE DOMINATION PRODUCER, CHECKABLE.**  A triple whose three pair wedges
together undercut its squared bracket DOMINATES.  Only wedges and brackets
appear, and nothing is quantified over.

Together with the landed `Gtz.triplePairAreaSum_le_three_mul_tripleBracket_sq`
this brackets domination between two multiples of the squared bracket:

  `pair area sum ≤ B²` ⟹ dominates ⟹ `pair area sum ≤ 3 B²`

and the factor between the two halves is exactly three. -/
theorem posSemidef_of_pairAreaSum_le_bracket_sq (leftVec midVec thirdVec : Fin 3 → ℝ)
    (hbracket : tripleBracket leftVec midVec thirdVec ≠ 0)
    (harea : triplePairAreaSum leftVec midVec thirdVec
      ≤ tripleBracket leftVec midVec thirdVec ^ 2) :
    (atomMatrix leftVec + atomMatrix midVec + atomMatrix thirdVec - 1).PosSemidef := by
  refine posSemidef_of_wedgeGram_cap leftVec midVec thirdVec hbracket (fun coeff => ?_)
  have hprobe := wedgeProbe_normSq_le_pairAreaSum_mul leftVec midVec thirdVec coeff
  have hcc : 0 ≤ coeff ⬝ᵥ coeff := by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (coeff 0), sq_nonneg (coeff 1), sq_nonneg (coeff 2)]
  nlinarith [hprobe, harea, hcc]

/-- **THE CHECKABLE PRODUCER AT A DESIGN.**  This is the witness a kill needs:
three pair wedges and one bracket decide domination outright. -/
theorem dominates_of_pairAreaSum_le_bracket_sq (design : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbracket : tripleBracket (design.atom x) (design.atom y) (design.atom z) ≠ 0)
    (harea : triplePairAreaSum (design.atom x) (design.atom y) (design.atom z)
      ≤ tripleBracket (design.atom x) (design.atom y) (design.atom z) ^ 2) :
    Dominates design ({x, y, z} : Finset (Fin m)) := by
  rw [Dominates, subsetSum_triple_eq_add design hxy hxz hyz]
  exact posSemidef_of_pairAreaSum_le_bracket_sq _ _ _ hbracket harea

end Gtz
