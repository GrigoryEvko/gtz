/-
# A decision cell that spends the MAGNITUDE of the oriented pairing product

`Gtz.Quantitative.GoodTripleGraph` proves that no certificate reading only SQUARED
pairings can close the covering: every such family lies inside the exact closure
`IsSignBlindGoodTriple`, and `not_signBlindGoodTripleCovering_seven` refutes that
closure at the frontier size, while `icosaDesign_dominates_iff_pairingProduct` shows
the discarded verdict is carried by the ORIENTATION of `p_ab p_ac p_bc` alone. A cell
that completes an atlas must therefore admit `excessGap < 0` and pay for it with a
LOWER bound on the oriented product.

`Gtz.dominates_of_coherentPairings` reads the SIGN of that product — it asks
`0 ≤ p_pa p_pb p_ab` — and then throws the MAGNITUDE away: its second hypothesis is,
term for term, `0 ≤ excessGap`. This file spends the magnitude:

  `PFC(productFloor)`   `0 ≤ pairMinor pivot pairFirst`
                        `0 ≤ pairMinor pivot pairSecond`
                        `productFloor · (u_p u_a u_b) ≤ p_pa p_pb p_ab`
                        `u_b p_pa² + u_a p_pb² + u_p p_ab²`
                              `≤ (1 + 2·productFloor) · (u_p u_a u_b)`

At `productFloor = 0` the last two hypotheses are exactly the coherent cell's, so
`PFC(0)` contains it (`isInCell_productFloorCell_zero_of_coherentPairings`). At
`productFloor > 0` the fourth hypothesis is a RELAXATION of `0 ≤ excessGap` by
`2·productFloor·U`, and the third pays for the relaxation out of the oriented product.
Every multiplier has degree zero and every inequality is non-strict, which is
mandatory: `(7,3)` sits on the ceiling (`not_gtzWeightedFloor_sevenThree_of_one_lt`
— if the conjecture holds there it holds with zero margin) and
`splitSevenDesign_no_strictBoxGoodPair` refutes the strict-inequality reading of the
box covering at that very size.

**WHAT THIS FILE IS NOT.** It is not the first `DecisionCell` in the repository —
`tautologicalCell` and `tautologicalCell_discharges` are shipped and audited. It is
not the first shipped cell to read the sign of the pairing product, and not the first
to reach `excessGap < 0`: `Gtz.dominates_of_twoMomentGap_nonneg` already does BOTH,
since `twoMomentGap = 4·e₃ + 4·e₂ − e₁²` carries the oriented product inside `e₃` and
imposes no sign on `excessGap` at all. That correction is recorded here as a theorem
(`twoMomentCell_reaches_negative_excessGap`) rather than as prose, because two
independent passes of this campaign asserted the opposite. What is new is the
particular trade — a nonzero lower bound on the ORIENTED product, bought against an
explicitly relaxed sign-blind aggregate — and the fact that it is the first
NON-TAUTOLOGICAL cell family wrapped into the `DecisionCell` interface, so that
`discriminantCovering_of_atlas` can consume it.

**MEASURED COVERAGE — A MEASUREMENT, NEVER A THEOREM.** On two optimiser-seeded pools
of exactified all-heavy `(7,3)` designs, the union of the shipped cell library
(sign-blind, coherent-sign, two-moment) covers `10311/10796 = 0.95508` of the first
pool and `10422/10800 = 0.96500` of the second; the product-floor family at the fixed
rational grid `{1/8, 1/4, 3/8}` covers `485/485` and `378/378` of the two residues.
Every one of those numbers is a MEASUREMENT on a pool that was produced by an
optimiser from one basin, not a statement about the parameter space, and NONE of them
is a covering theorem: no atlas built from this family is proved to cover, and the
true residue survives.

**CORRECTED — the `K4` claim that stood here was false, and self-contradictory.**
This paragraph used to end: the residue "survives at exactly rational points — the
`(6,3)` graphic design of `K4` and its `(7,3)` atom split have every leverage `3`,
Gram entries in `{3, ±3/2, 0}`, strictly dominating triples, and no shipped cell
firing at any triple." The final clause is FALSE, and it already contradicted the
measurement two sentences above it, which records the product-floor family covering
`485/485` and `378/378` of the residues. `Gtz.Quantitative.DecisionAtlasCellsSevenThree`
builds the object and settles it: at the star triple `{0,2,4}` of
`Gtz.graphicKFourDesign` the SHIPPED `Gtz.productFloorCell` fires at
`productFloor = 3/8`, a value on the very grid measured here
(`Gtz.isInCell_productFloorCell_threeEighths_graphicKFour`), with admissible window
`11/32 ≤ productFloor ≤ 27/64` (`Gtz.graphicKFour_productFloor_window`) — inside,
with room on both sides, not a knife edge. The `(7,3)` split falls the same way
(`Gtz.isInCell_productFloorCell_threeEighths_graphicKFourSeven`).

The rest of the claim IS confirmed, and proved rather than asserted: at that triple
the sign-blind closure fails (`Gtz.not_isSignBlindGoodTriple_graphicKFour_starTriple`),
the coherent-sign cell fails (`Gtz.graphicKFour_starTriple_excessGap_neg`), and the
two-moment certificate fails (`Gtz.graphicKFour_starTriple_twoMomentGap`). So the
honest statement is: the `K4` residue survives against THREE of the four shipped
families and is COVERED by the fourth.

Second correction, on scope: do NOT log the `(7,3)` half as a `(7,3)` obstruction
datum. `Gtz.graphicKFourSevenDesign` duplicates atom `0`, so it satisfies
`Gtz.HasParallelPair` and is NON-PRIMITIVE; `Gtz.dominating_of_parallel_pair` folds
it back one size, where the `(6,3)` original already dominates. It witnesses only
that the recorded claim was false at the frontier size, not a new obstruction there.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.GoodTripleGraph
import Gtz.Quantitative.TwoMomentCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

variable {m : ℕ}

/-! ### The cell -/

/-- **THE PRODUCT-FLOOR CELL.** A triple whose two pivot edges are compatible, whose
ORIENTED pairing product is at least `productFloor` times the excess product, and
whose sign-blind aggregate overshoots by at most twice that same amount, dominates.

The determinant leg is one addition:
`discriminantTie = excessGap + 2·(p_pa p_pb p_ab)`, the relaxed aggregate gives
`excessGap ≥ −2·productFloor·U`, and the product floor gives
`2·(p_pa p_pb p_ab) ≥ 2·productFloor·U`. The trace leg is the sum of the two
compatible pivot minors (`discriminantTrace_eq_pairMinor_add`). Every multiplier has
degree zero and no hypothesis is strict.

`productFloor` may be negative, in which case the cell is a RESTRICTION of the
coherent-sign cell rather than an extension; the interesting range is
`0 ≤ productFloor`, where the fourth hypothesis genuinely admits `excessGap < 0`. -/
theorem dominates_of_productFloor (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    {productFloor : ℝ}
    (hcompatFirst : 0 ≤ pairMinor D pivot pairFirst)
    (hcompatSecond : 0 ≤ pairMinor D pivot pairSecond)
    (hproduct : productFloor * (heavyExcess D pivot * heavyExcess D pairFirst
          * heavyExcess D pairSecond)
        ≤ atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
          * atomPairing D pairFirst pairSecond)
    (hrelaxedExcess : heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
          + heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
          + heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2
        ≤ (1 + 2 * productFloor) * (heavyExcess D pivot * heavyExcess D pairFirst
          * heavyExcess D pairSecond)) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  refine (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
    hpairDistinct hpivotHeavy).mpr ⟨?_, ?_⟩
  · rw [discriminantTrace_eq_pairMinor_add]
    linarith
  · rw [discriminantTie_eq_gramMinorForm]
    linarith

/-! ### The cell as a `DecisionCell`, and its discharge -/

/-- The product-floor cell as a `DecisionCell` of `Gtz.Quantitative.DecisionAtlasSevenThree`:
four sign conditions, each polynomial in the triple's six Gram scalars with rational
coefficients once `productFloor` is rational. The shipped sufficient-condition cell
families of that group are theorems with inline hypotheses, never `DecisionCell`
values, so this is the connection between the cell library and the atlas interface;
`tautologicalCell` is shipped but its sign conditions ARE the two legs. -/
noncomputable def productFloorCell (productFloor : ℝ)
    (pivot pairFirst pairSecond : Fin m) (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    DecisionCell m where
  signConditions :=
    [fun D => pairMinor D pivot pairFirst,
     fun D => pairMinor D pivot pairSecond,
     fun D => atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond
        - productFloor * (heavyExcess D pivot * heavyExcess D pairFirst
          * heavyExcess D pairSecond),
     fun D => (1 + 2 * productFloor) * (heavyExcess D pivot * heavyExcess D pairFirst
          * heavyExcess D pairSecond)
        - (heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
          + heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
          + heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2)]
  pivot := pivot
  pairFirst := pairFirst
  pairSecond := pairSecond
  pivotNePairFirst := hpivotFirst
  pivotNePairSecond := hpivotSecond
  pairFirstNePairSecond := hpairDistinct

/-- Membership in the cell, unfolded: the four sign conditions read back as the four
inequalities of `dominates_of_productFloor`. -/
theorem isInCell_productFloorCell_iff (D : WeightedDesign m 3) (productFloor : ℝ)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    IsInCell (productFloorCell productFloor pivot pairFirst pairSecond hpivotFirst
        hpivotSecond hpairDistinct) D
      ↔ (0 ≤ pairMinor D pivot pairFirst
          ∧ 0 ≤ pairMinor D pivot pairSecond
          ∧ productFloor * (heavyExcess D pivot * heavyExcess D pairFirst
              * heavyExcess D pairSecond)
            ≤ atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
              * atomPairing D pairFirst pairSecond
          ∧ heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
              + heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
              + heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2
            ≤ (1 + 2 * productFloor) * (heavyExcess D pivot * heavyExcess D pairFirst
              * heavyExcess D pairSecond)) := by
  constructor
  · intro hinCell
    simp only [IsInCell, productFloorCell, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hinCell
    obtain ⟨hcompatFirst, hcompatSecond, hproduct, hrelaxed⟩ := hinCell
    exact ⟨hcompatFirst, hcompatSecond, by linarith, by linarith⟩
  · rintro ⟨hcompatFirst, hcompatSecond, hproduct, hrelaxed⟩
    simp only [IsInCell, productFloorCell, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨hcompatFirst, hcompatSecond, by linarith, by linarith⟩

/-- **THE CELL OBLIGATION, DISCHARGED.** `DoesCellDischarge` for the product-floor
cell, at every parameter and every assigned triple of distinct atoms. This is the one
thing a certificate has to supply per cell; with it the cell plugs straight into
`discriminantCovering_of_atlas`, whose remaining hypothesis is that some finite list
of such cells COVERS — which nothing here supplies. -/
theorem doesCellDischarge_productFloorCell (productFloor : ℝ)
    (pivot pairFirst pairSecond : Fin m) (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    DoesCellDischarge (productFloorCell productFloor pivot pairFirst pairSecond
      hpivotFirst hpivotSecond hpairDistinct) := by
  intro D hheavy hinCell
  obtain ⟨hcompatFirst, hcompatSecond, hproduct, hrelaxed⟩ :=
    (isInCell_productFloorCell_iff D productFloor hpivotFirst hpivotSecond
      hpairDistinct).mp hinCell
  exact (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
    hpairDistinct (hheavy pivot)).mp
      (dominates_of_productFloor D hpivotFirst hpivotSecond hpairDistinct (hheavy pivot)
        (productFloor := productFloor) hcompatFirst hcompatSecond hproduct hrelaxed)

/-- **The atlas composition, spelled out once.** An atlas all of whose cells are
product-floor cells discharges, so `discriminantCovering_of_atlas` reduces
`DiscriminantCovering m` to COVERAGE alone. Stated so the interface fit is checked by
the kernel rather than asserted in prose; it supplies no coverage and therefore proves
nothing about `DiscriminantCovering`. -/
theorem doesAtlasDischarge_of_forall_productFloorCell (atlas : DecisionAtlas m)
    (hcells : ∀ cell ∈ atlas.cells, ∃ (productFloor : ℝ) (pivot pairFirst pairSecond : Fin m)
      (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
      (hpairDistinct : pairFirst ≠ pairSecond),
        cell = productFloorCell productFloor pivot pairFirst pairSecond hpivotFirst
          hpivotSecond hpairDistinct) :
    DoesAtlasDischarge atlas := by
  intro cell hcellMem
  obtain ⟨productFloor, pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond,
    hpairDistinct, hcellEq⟩ := hcells cell hcellMem
  rw [hcellEq]
  exact doesCellDischarge_productFloorCell productFloor pivot pairFirst pairSecond
    hpivotFirst hpivotSecond hpairDistinct

/-! ### Calibration against the shipped coherent-sign cell -/

/-- **`PFC(0)` CONTAINS THE SHIPPED COHERENT-SIGN CELL.** The two hypotheses of
`dominates_of_coherentPairings` put an all-heavy design into `productFloorCell 0` at
the same triple: the sign hypothesis is the third condition at `productFloor = 0`, the
aggregate hypothesis is the fourth, and the two pivot minors come from the aggregate
after cancelling the third excess. So the family loses nothing at the old parameter,
and `productFloor > 0` is a genuine extension rather than a re-parameterisation. -/
theorem isInCell_productFloorCell_zero_of_coherentPairings (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hfirstHeavy : 1 < leverageOf (D.atom pairFirst))
    (hsecondHeavy : 1 < leverageOf (D.atom pairSecond))
    (hcoherent : 0 ≤ atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond)
    (haggregate : heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
        + heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
        + heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2
      ≤ heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond) :
    IsInCell (productFloorCell 0 pivot pairFirst pairSecond hpivotFirst hpivotSecond
      hpairDistinct) D := by
  have hpivotPos : 0 < heavyExcess D pivot := by rw [heavyExcess]; linarith
  have hfirstPos : 0 < heavyExcess D pairFirst := by rw [heavyExcess]; linarith
  have hsecondPos : 0 < heavyExcess D pairSecond := by rw [heavyExcess]; linarith
  refine (isInCell_productFloorCell_iff D 0 hpivotFirst hpivotSecond hpairDistinct).mpr
    ⟨?_, ?_, by linarith, by linarith⟩
  · rw [pairMinor]
    have hscaled : heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
        ≤ heavyExcess D pairSecond
          * (heavyExcess D pivot * heavyExcess D pairFirst) := by
      nlinarith [haggregate,
        mul_nonneg hfirstPos.le (sq_nonneg (atomPairing D pivot pairSecond)),
        mul_nonneg hpivotPos.le (sq_nonneg (atomPairing D pairFirst pairSecond))]
    nlinarith [hscaled, hsecondPos]
  · rw [pairMinor]
    have hscaled : heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
        ≤ heavyExcess D pairFirst
          * (heavyExcess D pivot * heavyExcess D pairSecond) := by
      nlinarith [haggregate,
        mul_nonneg hsecondPos.le (sq_nonneg (atomPairing D pivot pairFirst)),
        mul_nonneg hpivotPos.le (sq_nonneg (atomPairing D pairFirst pairSecond))]
    nlinarith [hscaled, hfirstPos]

/-! ### The sign-blind half of domination, and the correction to the record -/

/-- **THE SHIPPED SIGN-BLIND CELL ALREADY COVERS THE WHOLE NONPOSITIVE-PRODUCT HALF OF
DOMINATION.** If a dominating triple of an all-heavy design has nonpositive oriented
product then `IsSignBlindGoodTriple` holds at it outright, because the absolute value
in that predicate then concedes exactly what the tie leg already granted. So every
dominating triple the sign-blind family misses has a STRICTLY POSITIVE oriented
product — which is exactly the quantity `icosaDesign_dominates_iff_pairingProduct`
identifies as carrying the verdict, and exactly the quantity the product floor bounds
below. -/
theorem isSignBlindGoodTriple_of_dominates_of_product_nonpos {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {first second third : Fin m} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hproductNonpos : atomPairing D first second * atomPairing D first third
      * atomPairing D second third ≤ 0)
    (hdominates : Dominates D {first, second, third}) :
    IsSignBlindGoodTriple D first second third := by
  have htie : 0 ≤ discriminantTie D first second third :=
    ((dominates_triple_iff_discriminantSystem D hfirstSecond hfirstThird hsecondThird
      (hheavy first)).mp hdominates).2
  rw [discriminantTie_eq_excessGap_add_tripleProduct] at htie
  rw [IsSignBlindGoodTriple, abs_of_nonpos hproductNonpos]
  linarith

/-- **THE CORRECTION TO THE RECORD, AS A THEOREM.** Two independent passes of this
campaign asserted that the shipped cell library cannot reach `excessGap < 0`, hence
that the union of the shipped cells is `{excessGap ≥ 0} ∩ {tie ≥ 0}` and that
`dominates_of_coherentPairings` is the only shipped cell reading the pairing sign. All
three statements are FALSE, and one six-scalar witness kills them: at leverages
`(4,4,4)` and pairings `(2,2,2)` the shipped `twoMomentGap` is `+7 ≥ 0` with total
leverage `12 > 3`, so `dominates_of_twoMomentGap_nonneg` fires, while the sign-blind
part of the tie leg is `3·3·3 − 3·(3·4) = −9 < 0`. Flipping one pairing to `−2` sends
`twoMomentGap` to `−121`, so the shipped cell is genuinely sign-sensitive as well.

SCOPE, and it is the whole scope: this is a statement about the six SCALARS a triple
presents, checked by `norm_num`. Nothing here claims a weighted `(7,3)` design
realises them at a triple, and the point does not need that — the shipped cell's
hypotheses are stated in exactly these scalars, so satisfying them at these values is
already enough to refute the three sentences above. -/
theorem twoMomentCell_reaches_negative_excessGap :
    0 ≤ twoMomentGap 4 4 4 2 2 2
      ∧ (3 : ℝ) < 4 + 4 + 4
      ∧ (4 - 1) * (4 - 1) * (4 - 1)
          - ((4 - 1) * (2 : ℝ) ^ 2 + (4 - 1) * (2 : ℝ) ^ 2 + (4 - 1) * (2 : ℝ) ^ 2) < 0
      ∧ twoMomentGap 4 4 4 2 2 (-2) < 0 := by
  refine ⟨?_, by norm_num, by norm_num, ?_⟩
  · rw [twoMomentGap]; norm_num
  · rw [twoMomentGap]; norm_num

end Gtz
