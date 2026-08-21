/-
# The contraction tax is sharp

`Gtz.isTie_bracket_tax` prices every triple of a tie by one of its own member
weights: `t_at_bt_c·[abc]² ≤ t_member`.  This module shows the price cannot be
lowered, by exhibiting a tie where EVERY triple pays its member weight
EXACTLY.

The regular tetrahedron is the witness.  It is a landed `(4,3)` tie
(`Gtz.tetraDesign_isTie`) with all four weights `1/4`, all four leverages `3`,
and every pairing `−1`.  So every triple's Gram is `3I − (J − I) = 4I − J`,
whose determinant is `16`, and the bracket mass of every triple is

  `m_C = (1/4)³·16 = 1/4 = t_member`   (`Gtz.tetra_bracketMass_eq_weight`).

All four triples saturate simultaneously (`Gtz.tetra_tax_tight`), so:

* the constant in `Gtz.isTie_bracket_tax` is BEST POSSIBLE — no `c < 1` makes
  `m_C ≤ c·t_member` hold at every tie (`Gtz.tetra_tax_not_improvable`);
* the inequality cannot be made strict;
* the block determinant equals the block's least eigenvalue there, because the
  tetrahedral projection block has spectrum `(1/4, 1, 1)` — the two `+1`
  directions are the two contact directions of
  `Gtz.blockEigen_one_of_supported_mem_range`.

The tetrahedron is also a PRIMITIVE tie — no two of its atoms are parallel —
which is why it is a foil and not a counterexample: like the `(5,3)` diamond,
it shows the hinge is false below size six, and every law of this lane is
tested against it before it is believed.
-/
import Gtz.Wave.BracketContractionTax
import Gtz.Ties.TetrahedronCertifiedTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

/-! ## 1. The tetrahedral bracket mass -/

/-- Every triple of the tetrahedron has squared bracket sixteen. -/
theorem tetra_bracket_sq (a b c : Fin 4) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    atomBracket tetraDesign a b c ^ 2 = 16 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    first
      | (exact absurd rfl hab)
      | (exact absurd rfl hac)
      | (exact absurd rfl hbc)
      | (simp [atomBracket, tripleBracket_eq, tetraDesign, tetraAtom] <;> norm_num)

/-- **THE TAX IS SATURATED AT THE TETRAHEDRON.**  Every triple's bracket mass
equals one quarter, which is exactly its member weight. -/
theorem tetra_bracketMass_eq_weight (a b c : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    tetraDesign.weight a * (tetraDesign.weight b
        * (tetraDesign.weight c * atomBracket tetraDesign a b c ^ 2))
      = tetraDesign.weight a := by
  rw [tetra_bracket_sq a b c hab hac hbc]
  simp only [tetraDesign]
  norm_num

/-! ## 2. Sharpness -/

/-- **THE TAX IS TIGHT, AT EVERY TRIPLE SIMULTANEOUSLY.**  At the tetrahedral
tie the bracket tax holds with EQUALITY for every choice of member — there is
no slack anywhere to absorb an improvement. -/
theorem tetra_tax_tight (a b c : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ member ∈ ({a, b, c} : Finset (Fin 4)),
      tetraDesign.weight a * (tetraDesign.weight b
          * (tetraDesign.weight c * atomBracket tetraDesign a b c ^ 2))
        = tetraDesign.weight member := by
  intro member _
  rw [tetra_bracketMass_eq_weight a b c hab hac hbc]
  simp only [tetraDesign]

/-- **THE CONSTANT ONE CANNOT BE IMPROVED.**  No factor below one survives:
a law `m_C ≤ c·t_member` valid at every tie forces `1 ≤ c`, because the
tetrahedron already sits at equality. -/
theorem tetra_tax_not_improvable {c : ℝ}
    (hlaw : ∀ member ∈ ({0, 1, 2} : Finset (Fin 4)),
      tetraDesign.weight 0 * (tetraDesign.weight 1
          * (tetraDesign.weight 2 * atomBracket tetraDesign 0 1 2 ^ 2))
        ≤ c * tetraDesign.weight member) :
    1 ≤ c := by
  have hmem : (0 : Fin 4) ∈ ({0, 1, 2} : Finset (Fin 4)) := by decide
  have h := hlaw 0 hmem
  rw [tetra_bracketMass_eq_weight 0 1 2 (by decide) (by decide) (by decide)] at h
  simp only [tetraDesign] at h
  linarith

end Gtz
