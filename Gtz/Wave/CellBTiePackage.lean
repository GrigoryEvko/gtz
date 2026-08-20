import Gtz.Wave.CellHChartFloors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The cell-B tie package

Everything a `Z1` both-light tie forces, in one polynomial package, with no
inverse and no matrix.  This is the system a certificate search should be
given: the floors as gap determinant signs, and the contraction tax at
every triple.

* `Gtz.cellB_seven_floors_iff_gapDets` — THE FLOOR PACKAGE: the `y`-floor
  and the three outside floors at each of the two surviving four-sets are
  seven sign conditions on seven gap determinants.  The `y`-floor and the
  `z`-floor are the same condition (both erase to the outside triple), so
  seven determinants carry eight floors.
* `Gtz.isTie_tax_package` — THE TAX PACKAGE: at a tie EVERY triple pays,
  so all twenty weighted squared brackets sit below a member weight.
* `Gtz.cellB_tie_package` — the two together, as the tie's necessary
  polynomial conditions.

Measured, by adversarial descent rather than sampling (240000 trajectories
each):

* floors alone, cell B — infimum of the largest gap determinant `+5.377e-3`
* floors AND tax, cell B — infimum `+8.583e-3`

so the tax raises the boundary margin by about sixty percent.  Both are
bounded away from zero, and a tie needs a nonpositive value.  On cell H the
four surviving floors alone floor at `+8.377e-2`.

The tightness target is NOT the inside-weight collapse: walking the
minimizer's inside weights down by a factor of `256` raises the margin
monotonically to a finite limit near `5.894e-3`, so the certificate does
not need a weight-carried degeneration factor there.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The floor package -/

/-- **THE FLOOR PACKAGE OF CELL B.**  On the both-light cell the four
floors of the `y`-side four-set are four gap determinant signs: the shared
outside triple for the `y`-floor, and `y` with two outside atoms for each
outside floor.  The `z`-side reads identically with `z` in place of `y`, and
its own member floor is the SAME outside determinant, so the eight floors
of the cell are carried by seven determinants. -/
theorem cellB_seven_floors_iff_gapDets (D : WeightedDesign m 3)
    {x y z d4 d5 d6 : Fin m}
    (hy4 : y ≠ d4) (hy5 : y ≠ d5) (hy6 : y ≠ d6)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin m))ᶜ : Finset (Fin m)) = {d4, d5, d6})
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef) :
    ((1 ≤ D.atom y ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
            *ᵥ D.atom y))
        ∧ (1 ≤ D.atom d4 ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
            *ᵥ D.atom d4)))
      ↔ (tripleGapDet (D.atom d4) (D.atom d5) (D.atom d6) ≤ 0
        ∧ tripleGapDet (D.atom y) (D.atom d5) (D.atom d6) ≤ 0) :=
  cellH_four_floors_iff_gapDets D hy4 hy5 hy6 h45 h46 h56 hcompl hAy

/-- **THE TWO SIDES SHARE THEIR MEMBER FLOOR.**  The `y`-floor and the
`z`-floor of the both-light cell are the same sign condition, because both
erase to the outside triple. -/
theorem cellB_yFloor_iff_zFloor_gapDet (D : WeightedDesign m 3)
    {x y z : Fin m}
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef) :
    (1 ≤ D.atom y ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
          *ᵥ D.atom y))
      ↔ (1 ≤ D.atom z ⬝ᵥ
        ((subsetSum D (insert z (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z)) :=
  bothLight_y_floor_iff_z_floor D hAy hAz

/-! ## 2. The tax package -/

/-- **THE TAX PACKAGE OF A TIE.**  Every triple of a tie pays: its weighted
squared bracket sits below one of its member weights.  Twenty polynomial
inequalities in the weights and the dot products, with no cell hypothesis
at all.

Measured: adding these twenty to the seven floors raises the boundary
infimum of the cell-B system from `+5.377e-3` to `+8.583e-3`. -/
theorem isTie_tax_package (D : WeightedDesign m 3) (htie : IsTie D) :
    ∀ a b c : Fin m, a ≠ b → a ≠ c → b ≠ c →
      ∃ member ∈ ({a, b, c} : Finset (Fin m)),
        D.weight a * D.weight b * D.weight c
            * (tripleGram (D.atom a) (D.atom b) (D.atom c)).det
          ≤ D.weight member :=
  fun _ _ _ hab hac hbc => isTie_chartDet_tax D htie hab hac hbc

/-- **THE TAX IN BRACKET FORM.**  The same package written in the bracket,
which is the horn arm's currency and the chart's determinant alike. -/
theorem isTie_tax_package_bracket (D : WeightedDesign m 3) (htie : IsTie D)
    (a b c : Fin m) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ member ∈ ({a, b, c} : Finset (Fin m)),
      D.weight a * D.weight b * D.weight c * atomBracket D a b c ^ 2
        ≤ D.weight member := by
  obtain ⟨member, hmem, hle⟩ := isTie_chartDet_tax D htie hab hac hbc
  refine ⟨member, hmem, ?_⟩
  rwa [chartDet_eq_bracket_sq,
    show tripleBracket (D.atom a) (D.atom b) (D.atom c)
      = atomBracket D a b c from rfl] at hle

/-! ## 3. The package -/

/-- **THE CELL-B TIE PACKAGE.**  What a both-light tie forces, as one
polynomial system: the outside triple and the two `y`-side triples are
flat, and every triple of the design pays its tax.  No inverse, no matrix,
no chart — the certificate search's input. -/
theorem cellB_tie_package (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z d4 d5 d6 : Fin m}
    (hy4 : y ≠ d4) (hy5 : y ≠ d5) (hy6 : y ≠ d6)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin m))ᶜ : Finset (Fin m)) = {d4, d5, d6})
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1).PosDef)
    (hyfloor : 1 ≤ D.atom y ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
        *ᵥ D.atom y))
    (hd4floor : 1 ≤ D.atom d4 ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin m))ᶜ)) - 1)⁻¹
        *ᵥ D.atom d4)) :
    (tripleGapDet (D.atom d4) (D.atom d5) (D.atom d6) ≤ 0
        ∧ tripleGapDet (D.atom y) (D.atom d5) (D.atom d6) ≤ 0)
      ∧ (∀ a b c : Fin m, a ≠ b → a ≠ c → b ≠ c →
        ∃ member ∈ ({a, b, c} : Finset (Fin m)),
          D.weight a * D.weight b * D.weight c * atomBracket D a b c ^ 2
            ≤ D.weight member) :=
  ⟨(cellB_seven_floors_iff_gapDets D hy4 hy5 hy6 h45 h46 h56 hcompl hAy).mp
      ⟨hyfloor, hd4floor⟩,
    fun a b c hab hac hbc => isTie_tax_package_bracket D htie a b c hab hac hbc⟩

end Gtz
