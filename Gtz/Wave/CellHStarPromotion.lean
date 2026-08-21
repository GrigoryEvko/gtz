/-
# The star promotion: a positive gap determinant is domination, at a fixed atom

`Gtz.cellH_exists_tripleGap_pos` produces a triple of cell H with a positive gap
DETERMINANT.  A positive determinant is not domination — the Sylvester criterion
needs all three leading minors, and a triple built on an inadmissible pair can
carry a positive determinant while failing the first two.  The corner arm's
promotion `Gtz.tripleGram_posDef_iff_gapDet_pos_of_admissible` repairs exactly
that, but it is stated over ONE PAIR with the third atom free, and the cell-H
trio has the opposite index shape: ONE ATOM fixed, and the PAIR varying over the
three pairs of the outside triple.

The two shapes are not the same statement, and no promotion between them was
landed.  This module supplies it.

## The star is the right index shape

The three triples of the trio are `{x,c,d}`, `{x,b,d}` and `{x,b,c}` — the star
of the fixed atom `x` over `{b,c,d}`.  Every one of them contains a pair THROUGH
`x`, so the corner arm's promotion applies to each with a pair the fixed atom
belongs to:

* `{x,c,d}` through `(x,c)`,
* `{x,b,d}` through `(x,b)`,
* `{x,b,c}` through `(x,b)`.

So TWO admissible pairs through the fixed atom promote the whole trio
(`Gtz.star_exists_posDef_of_exists_gapDet_pos`), and a fixed atom whose star is
admissible supplies them at once
(`Gtz.star_exists_posDef_of_admissibleStar`).  This is where the per-vertex law
`Σ_c t_c·pairGapMinor(g_x,g_c) = ℓ_x − 2` enters: admissibility of the star of
an atom is governed by that atom's leverage alone.

## What it closes

Chained against the trio, cell H now produces a STRICTLY DOMINATING TRIPLE
rather than a positive determinant (`Gtz.cellH_exists_dominating_triple`).  A
tie admits no strictly dominating triple, so this is the shape the cell fight
needs.

The ambient form is what the cell laws are written in, so the module also lands
the raw-vector Gram bridge (`Gtz.atomTriple_posDef_iff_tripleGram`), the
three-atom analogue of the landed design-level `Gtz.subsetSum_posDef_iff_tripleGram`.
-/
import Gtz.Wave.CellHDowndateLaws
import Gtz.Wave.OppositeHornSelect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

/-! ## 1. The raw-vector Gram bridge -/

/-- Three atoms sum to the column matrix times its transpose. -/
theorem atomTriple_eq_mul_transpose (a b c : Fin 3 → ℝ) :
    atomMatrix a + atomMatrix b + atomMatrix c
      = columnMatrix a b c * (columnMatrix a b c)ᵀ := by
  ext i j
  simp [columnMatrix, Matrix.mul_apply, atomMatrix, Matrix.vecMulVec_apply,
    Fin.sum_univ_three, Matrix.transpose_apply]

/-- **THE GRAM CRITERION AT RAW VECTORS.**  The three-atom analogue of the
landed design-level bridge: strict domination by three atoms is positive
definiteness of their Gram less the identity. -/
theorem atomTriple_posDef_iff_tripleGram (a b c : Fin 3 → ℝ) :
    (atomMatrix a + atomMatrix b + atomMatrix c - 1).PosDef
      ↔ (tripleGram a b c - 1).PosDef := by
  rw [atomTriple_eq_mul_transpose, tripleGram]
  exact (posDef_transpose_mul_sub_one_comm _).symm

/-- **THE PROMOTION, IN AMBIENT FORM.**  Over an admissible pair with heavy
trace, a positive gap determinant IS strict domination — stated for the matrix
sum the cell laws are written in. -/
theorem atomTriple_posDef_iff_gapDet_pos_of_admissible {a b c : Fin 3 → ℝ}
    (hmin : 0 < pairGapMinor a b) (htr : 2 < leverageOf a + leverageOf b) :
    (atomMatrix a + atomMatrix b + atomMatrix c - 1).PosDef
      ↔ 0 < (atomMatrix a + atomMatrix b + atomMatrix c - 1).det := by
  rw [atomTriple_posDef_iff_tripleGram, gapDet_triple_eq_tripleGapDet]
  exact tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr

/-! ## 2. The star promotion -/

/-- **THE STAR PROMOTION.**  Two admissible pairs through the fixed atom promote
the whole trio: every triple of the star `{x,c,d}`, `{x,b,d}`, `{x,b,c}`
contains one of them, so a positive gap determinant anywhere in the trio is
strict domination there.

This is the index shape the cell-H trio has, and it is NOT the corner arm's
one-pair-three-atoms statement. -/
theorem star_exists_posDef_of_exists_gapDet_pos {x b c d : Fin 3 → ℝ}
    (hxb : 0 < pairGapMinor x b) (htb : 2 < leverageOf x + leverageOf b)
    (hxc : 0 < pairGapMinor x c) (htc : 2 < leverageOf x + leverageOf c)
    (hdet : 0 < (atomMatrix x + atomMatrix c + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix x + atomMatrix b + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix x + atomMatrix b + atomMatrix c - 1).det) :
    (atomMatrix x + atomMatrix c + atomMatrix d - 1).PosDef
      ∨ (atomMatrix x + atomMatrix b + atomMatrix d - 1).PosDef
      ∨ (atomMatrix x + atomMatrix b + atomMatrix c - 1).PosDef := by
  rcases hdet with h | h | h
  · exact Or.inl ((atomTriple_posDef_iff_gapDet_pos_of_admissible hxc htc).mpr h)
  · exact Or.inr (Or.inl ((atomTriple_posDef_iff_gapDet_pos_of_admissible hxb htb).mpr h))
  · exact Or.inr (Or.inr ((atomTriple_posDef_iff_gapDet_pos_of_admissible hxb htb).mpr h))

/-- **THE STAR PROMOTION FROM AN ADMISSIBLE STAR.**  A fixed atom whose three
pairs into the outside triple are all admissible supplies the hypotheses at
once.  Admissibility of a star is governed by the atom's leverage alone, through
the per-vertex law. -/
theorem star_exists_posDef_of_admissibleStar {x b c d : Fin 3 → ℝ}
    (hxb : 0 < pairGapMinor x b) (hxc : 0 < pairGapMinor x c)
    (hxd : 0 < pairGapMinor x d)
    (htb : 2 < leverageOf x + leverageOf b)
    (htc : 2 < leverageOf x + leverageOf c)
    (htd : 2 < leverageOf x + leverageOf d)
    (hdet : 0 < (atomMatrix x + atomMatrix c + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix x + atomMatrix b + atomMatrix d - 1).det
      ∨ 0 < (atomMatrix x + atomMatrix b + atomMatrix c - 1).det) :
    (atomMatrix x + atomMatrix c + atomMatrix d - 1).PosDef
      ∨ (atomMatrix x + atomMatrix b + atomMatrix d - 1).PosDef
      ∨ (atomMatrix x + atomMatrix b + atomMatrix c - 1).PosDef := by
  have := hxd; have := htd
  exact star_exists_posDef_of_exists_gapDet_pos hxb htb hxc htc hdet

/-! ## 3. Cell H produces a dominator -/

/-- **CELL H PRODUCES A STRICTLY DOMINATING TRIPLE.**  The trio's symmetric-
function disjunction gives a positive gap determinant somewhere in the star of
the inserted atom, and two admissible pairs through that atom promote it to
strict domination.

A tie admits no strictly dominating triple, so this is the form the cell fight
consumes. -/
theorem cellH_exists_dominating_triple (lam : ℝ) (u ax ay az b c d : Fin 3 → ℝ)
    (hcorner : atomMatrix ax + atomMatrix ay + atomMatrix az - 1
      = lam • atomMatrix u)
    (hayb : 0 < pairGapMinor ay b) (htb : 2 < leverageOf ay + leverageOf b)
    (hayc : 0 < pairGapMinor ay c) (htc : 2 < leverageOf ay + leverageOf c)
    (hdisj :
      dotProduct ax
          ((atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1).adjugate
            *ᵥ ax)
        + dotProduct az
          ((atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1).adjugate
            *ᵥ az)
        < lam * dotProduct u
          ((atomMatrix ay + atomMatrix b + atomMatrix c + atomMatrix d - 1).adjugate
            *ᵥ u)
      ∨ (atomMatrix ay + atomMatrix c + atomMatrix d - 1).det
            * (atomMatrix ay + atomMatrix b + atomMatrix d - 1).det
          + (atomMatrix ay + atomMatrix c + atomMatrix d - 1).det
            * (atomMatrix ay + atomMatrix b + atomMatrix c - 1).det
          + (atomMatrix ay + atomMatrix b + atomMatrix d - 1).det
            * (atomMatrix ay + atomMatrix b + atomMatrix c - 1).det < 0
      ∨ 0 < (atomMatrix ay + atomMatrix c + atomMatrix d - 1).det
            * ((atomMatrix ay + atomMatrix b + atomMatrix d - 1).det
              * (atomMatrix ay + atomMatrix b + atomMatrix c - 1).det)) :
    (atomMatrix ay + atomMatrix c + atomMatrix d - 1).PosDef
      ∨ (atomMatrix ay + atomMatrix b + atomMatrix d - 1).PosDef
      ∨ (atomMatrix ay + atomMatrix b + atomMatrix c - 1).PosDef :=
  star_exists_posDef_of_exists_gapDet_pos hayb htb hayc htc
    (cellH_exists_tripleGap_pos lam u ax ay az b c d hcorner hdisj)

end Gtz
