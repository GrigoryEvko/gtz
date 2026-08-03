/-
# Two new decision cells, the certificate-shape question CLOSED, and the K4 residue claim REFUTED

`Gtz.Quantitative.DecisionAtlasSevenThree` fixes the atlas interface and proves it
lossless; `Gtz.Quantitative.SignReadingCell` supplies the first non-tautological
`DecisionCell`. This file adds two cell families, settles what a cell family can and
cannot buy, and corrects one recorded claim about where the residue lives.

**PROVED — two new cell families, both wrapped into the interface.**

*Cell A, the conditional-pairing box.* With `conditionalPairing = u_p p_ab − p_pa p_pb`
(the square in `pairMinor_product_eq_tieSchur`, named), a triple dominates as soon as
its two pivot minors are nonnegative and `|conditionalPairing|` is bounded by each
minor scaled by a parameter, the two parameters having product at most one
(`dominates_of_conditionalPairingBox`). EVERY hypothesis has DEGREE at most TWO in the
six Gram scalars, against degree three for the tie leg it certifies. The multipliers are
NOT degree zero, unlike the product-floor cell's: the certificate multiplies the two
bounds together and scales the parameter constraint by both minors. The unit member is
`dominates_of_unitConditionalPairingBox`. `conditionalPairingBoxCell` +
`doesCellDischarge_conditionalPairingBoxCell` are the `DecisionCell` form.

*Cell B, the pairing-floor cell.* The product-floor cell's degree-three hypothesis on
the oriented product, replaced by three DEGREE-ONE bounds `floor ≤ p` on the edges plus
the relaxed gap `−2·floor³ ≤ excessGap` (`dominates_of_pairingFloor`,
`pairingFloorCell`, `doesCellDischarge_pairingFloorCell`). The sign of the product is
not assumed; it is derived from three edge inequalities.

**PROVED — the certificate-SHAPE question is closed; only the TRIPLE is left.** Cell A
is EXACTLY COMPLETE at every triple (`exists_conditionalPairingBox_iff_dominates`), and
so is the shipped product-floor family (`exists_productFloor_iff_dominates`, whose
witness is the exact ratio `productFloor = p_pa p_pb p_ab / (u_p u_a u_b)`). Hence
`DiscriminantCovering m` IS a covering by degree-two cells
(`discriminantCovering_iff_conditionalPairingCovering`) and, at the frontier size, so is
the whole of rank three (`conditionalPairingCovering_seven_iff_rank_three`). This
upgrades `SignReadingCell`'s own caveat "no atlas built from this family is proved to
cover" into a localisation: NO cell family can enlarge the per-triple reach, so the
residue is entirely the two CHOICES — which triple, and which parameters.

**REFUTED — the recorded K4 residue claim.** `Gtz.Quantitative.SignReadingCell` records
that the surviving residue "survives at exactly rational points — the `(6,3)` graphic
design of `K4` and its `(7,3)` atom split have every leverage `3`, Gram entries in
`{3, ±3/2, 0}`, strictly dominating triples, and no shipped cell firing at any triple."
The last clause is FALSE. `graphicKFourDesign` is that object, built here for the first
time: six atoms `sqrt(6)/2 · (1,1,0), (1,−1,0), (1,0,1), (1,0,−1), (0,1,1), (0,1,−1)` at
uniform weight `1/6`, exactly Parseval, every leverage exactly `3`, Gram off-diagonal in
`{0, ±3/2}` with the three zeros on the three perfect matchings of `K4`. At its star
triple `{0,2,4}` — three edges through one vertex, all three pairings `+3/2` — the
SHIPPED `Gtz.productFloorCell` fires at `productFloor = 3/8`, a value ON the rational
grid `{1/8, 1/4, 3/8}` the same file reports measuring
(`isInCell_productFloorCell_threeEighths_graphicKFour`). The exact admissible window is
`11/32 ≤ productFloor ≤ 27/64` (`graphicKFour_productFloor_window`), so `3/8 = 24/64`
sits inside with room on both sides — not a knife edge. The `(7,3)` atom split is
refuted the same way (`isInCell_productFloorCell_threeEighths_graphicKFourSeven`), which
is the size that carries rank three.

The REST of the recorded claim is CONFIRMED, and proved rather than asserted: at that
triple the sign-blind closure fails (`excessGap = −11/2` against `2·|27/8| = 27/4`,
`not_isSignBlindGoodTriple_graphicKFour_starTriple`); the coherent-sign cell fails
because its aggregate hypothesis IS `0 ≤ excessGap`
(`graphicKFour_starTriple_excessGap_neg`); and the two-moment certificate fails with gap
exactly `−10` (`graphicKFour_starTriple_twoMomentGap`). So the correct statement is: the
K4 residue survives against THREE of the four shipped families, and is covered by the
fourth. Both new cells fire there too
(`graphicKFourDesign_dominates_starTriple_of_unitConditionalBox`, `..._of_pairingFloor`).

**PROVED — non-subsumption by the radius-box family, as a theorem.**
`isSignBlindGoodTriple_of_radiusBox` discharges, for EVERY admissible triple of radii,
the containment of the radius-box family in the sign-blind closure — `GoodTripleGraph`
records that containment in prose and proves it only for the symmetric box. With it,
`no_radiusBox_at_graphicKFour_starTriple` shows NO admissible radius box whatsoever
contains the K4 star triple, so the new cells are not a reparametrisation of the shipped
box family at that triple. Non-subsumption of the coherent-sign cell is
`graphicKFour_starTriple_excessGap_neg`, since that cell's aggregate hypothesis is
`0 ≤ excessGap` term for term.

**NOT PROVED — the exact remaining gap.**

* NO COVERAGE. Not one theorem here supplies `DoesAtlasCover`. Completeness is
  PER TRIPLE and PER REAL PARAMETER; it says nothing about a finite list of cells.
* THE PARAMETERS ARE REAL, AND THE BOUNDARY FORCES THEM. At the regular tetrahedron the
  unit member is tight in all four inequalities and the constraint `param·param ≤ 1`
  holds with EQUALITY (`unitConditionalPairingBox_tight_at_tetraDesign`), matching
  `tetraDesign_discriminantTie = 0`. So a tie-boundary triple must be entered with the
  exact ratio, and whether finitely many RATIONAL parameter pairs suffice at `(7,3)` is
  open. This is the residue the degree reduction leaves; it is combinatorial and
  arithmetic, not analytic.
* NO DESIGN OUTSIDE THE SHIPPED UNION. This lane exhibits no all-heavy design at which
  every shipped cell fails at every triple — the K4 object was the recorded candidate
  and it is covered. Whether one exists is open; by the completeness theorems such a
  design would have to fail on the PARAMETER GRID, never on the certificate shape.
* CELL B IS STRICTLY WEAKER THAN CELL A, not complementary: its floor must be
  nonnegative, and the tetrahedron's pairings are all `−1`
  (`pairingFloorCell_blind_at_tetraDesign`). It reaches the acute over-unit stratum
  where the sign-blind body fails; it misses the obtuse tie boundary entirely.
* THE TWO PIVOT-MINOR HYPOTHESES CANNOT BE DROPPED, with an exact witness: excesses
  `(2,1,1)` and pairings `(2,2,2)` give a strictly positive tie leg and a strictly
  negative trace leg (`tieLeg_alone_does_not_imply_traceLeg`). That is a statement about
  the six scalars, realised by `(1,1,1), (1,1,0), (1,1,0)` in `R³`; whether a weighted
  `(7,3)` design presents them at a triple is not established, and the realising triple
  has two equal vectors so it is non-primitive.
* The nonnegativity of the two parameters of Cell A is NOT assumed anywhere — the proof
  does not need it, so the family is stated at its weakest true hypotheses.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Quantitative.SignReadingCell

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

variable {m : ℕ}

/-! ### The conditional pairing: the square in the Schur identity, named -/

/-- The **conditional pairing** `u_p p_ab − p_pa p_pb` of a triple at its pivot: the
numerator of the partial correlation `rho_ab − rho_pa rho_pb` after clearing the
square roots. It is exactly the quantity squared in `pairMinor_product_eq_tieSchur`,
so the tie leg is the pivot excess dividing the gap between the two pivot minors'
product and this square. Degree two in the six Gram scalars, and it reads the
ORIENTED product `p_pa p_pb p_ab` inside its square rather than the magnitude. -/
def conditionalPairing (D : WeightedDesign m 3) (pivot pairFirst pairSecond : Fin m) : ℝ :=
  heavyExcess D pivot * atomPairing D pairFirst pairSecond
    - atomPairing D pivot pairFirst * atomPairing D pivot pairSecond

/-- The Schur identity of `pairMinor_product_eq_tieSchur`, restated with the
conditional pairing named. -/
theorem pairMinor_product_eq_tie_add_conditionalPairing_sq (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    pairMinor D pivot pairFirst * pairMinor D pivot pairSecond
      = heavyExcess D pivot * discriminantTie D pivot pairFirst pairSecond
        + conditionalPairing D pivot pairFirst pairSecond ^ 2 := by
  rw [conditionalPairing]
  exact pairMinor_product_eq_tieSchur D pivot pairFirst pairSecond

/-- The tie leg, solved for: the pivot excess times the tie leg is the gap between
the product of the two pivot minors and the squared conditional pairing. -/
theorem heavyExcess_mul_discriminantTie_eq (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    heavyExcess D pivot * discriminantTie D pivot pairFirst pairSecond
      = pairMinor D pivot pairFirst * pairMinor D pivot pairSecond
        - conditionalPairing D pivot pairFirst pairSecond ^ 2 := by
  rw [pairMinor_product_eq_tie_add_conditionalPairing_sq]
  ring

/-! ### Cell A: the conditional-pairing box, degree two and exactly complete -/

/-- **THE CONDITIONAL-PAIRING BOX CELL.** Two parameters whose PRODUCT is at most one,
the two pivot minors nonnegative, and the conditional pairing bounded by each minor
scaled by its parameter. Every hypothesis has DEGREE at most TWO in the triple's six
Gram scalars — the tie leg it certifies has degree three — but the MULTIPLIERS are not
degree zero: `1 − paramFirst·paramSecond` is scaled by `pairMinor · pairMinor` and the
two bounds are multiplied by each other, so this family does NOT inherit the
degree-zero-multiplier certificate of `Gtz.productFloorCell`. Only the sign conditions
drop a degree. The parameters are NOT assumed nonnegative: the two bounds
already force `0 ≤ paramFirst · pairMinor` and `0 ≤ paramSecond · pairMinor`, so the
family is stated at its weakest true hypotheses.

The certificate is one line of arithmetic: the two bounds multiply to
`conditionalPairing² ≤ (paramFirst · paramSecond) · pairMinor · pairMinor
≤ pairMinor · pairMinor`, which is `0 ≤ heavyExcess pivot · discriminantTie` by
`heavyExcess_mul_discriminantTie_eq`; the trace leg is the sum of the two minors by
`discriminantTrace_eq_pairMinor_add`. -/
theorem dominates_of_conditionalPairingBox (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    {paramFirst paramSecond : ℝ} (hparamProduct : paramFirst * paramSecond ≤ 1)
    (hminorFirst : 0 ≤ pairMinor D pivot pairFirst)
    (hminorSecond : 0 ≤ pairMinor D pivot pairSecond)
    (hboundFirst : |conditionalPairing D pivot pairFirst pairSecond|
      ≤ paramFirst * pairMinor D pivot pairFirst)
    (hboundSecond : |conditionalPairing D pivot pairFirst pairSecond|
      ≤ paramSecond * pairMinor D pivot pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  have hpivotPos : 0 < heavyExcess D pivot := by rw [heavyExcess]; linarith
  have habsNonneg : 0 ≤ |conditionalPairing D pivot pairFirst pairSecond| := abs_nonneg _
  have hminorProductNonneg : 0 ≤ pairMinor D pivot pairFirst * pairMinor D pivot pairSecond :=
    mul_nonneg hminorFirst hminorSecond
  have hsquareBound : conditionalPairing D pivot pairFirst pairSecond ^ 2
      ≤ (paramFirst * pairMinor D pivot pairFirst)
        * (paramSecond * pairMinor D pivot pairSecond) := by
    have hproduct : |conditionalPairing D pivot pairFirst pairSecond|
        * |conditionalPairing D pivot pairFirst pairSecond|
        ≤ (paramFirst * pairMinor D pivot pairFirst)
          * (paramSecond * pairMinor D pivot pairSecond) :=
      mul_le_mul hboundFirst hboundSecond habsNonneg (le_trans habsNonneg hboundFirst)
    rw [abs_mul_abs_self] at hproduct
    nlinarith [hproduct]
  have hslack : (paramFirst * pairMinor D pivot pairFirst)
      * (paramSecond * pairMinor D pivot pairSecond)
      ≤ pairMinor D pivot pairFirst * pairMinor D pivot pairSecond := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - paramFirst * paramSecond)
      hminorProductNonneg]
  have htieScaled : 0 ≤ heavyExcess D pivot
      * discriminantTie D pivot pairFirst pairSecond := by
    rw [heavyExcess_mul_discriminantTie_eq]
    linarith
  refine (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
    hpairDistinct hpivotHeavy).mpr ⟨?_, ?_⟩
  · rw [discriminantTrace_eq_pairMinor_add]
    linarith
  · exact (mul_nonneg_iff_of_pos_left hpivotPos).mp htieScaled

/-- The symmetric unit member `paramFirst = paramSecond = 1`: the conditional pairing
bounded by BOTH pivot minors. No parameter at all, and still degree two. -/
theorem dominates_of_unitConditionalPairingBox (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    (hboundFirst : |conditionalPairing D pivot pairFirst pairSecond|
      ≤ pairMinor D pivot pairFirst)
    (hboundSecond : |conditionalPairing D pivot pairFirst pairSecond|
      ≤ pairMinor D pivot pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond} :=
  dominates_of_conditionalPairingBox D hpivotFirst hpivotSecond hpairDistinct hpivotHeavy
    (paramFirst := 1) (paramSecond := 1) (by norm_num)
    (le_trans (abs_nonneg _) hboundFirst) (le_trans (abs_nonneg _) hboundSecond)
    (by simpa using hboundFirst) (by simpa using hboundSecond)

/-- **THE CONDITIONAL-PAIRING BOX FAMILY IS EXACTLY COMPLETE AT EVERY TRIPLE.** At a
triple of distinct atoms of an all-heavy design, domination is EQUIVALENT to the
existence of two parameters putting the triple in the box. So nothing is lost by
replacing the degree-three tie leg with the degree-two box: the covering at rank three
is a disjunction of DEGREE-TWO conditions, with two real parameters per cell.

Forward direction: `pairMinor_nonneg_of_dominates` supplies both minors, the Schur
identity supplies `conditionalPairing² ≤ pairMinor · pairMinor`, and the parameters are
the two ratios `|conditionalPairing| / pairMinor` — or both zero when a minor
vanishes, which forces the conditional pairing to vanish too.

SCOPE. The parameters are REAL. A finite atlas needs finitely many, and at a triple
on the tie boundary the box must be entered with equality, so the exact ratios are
forced; whether finitely many rational pairs suffice at `(7,3)` is NOT settled here
and is the residue this reformulation leaves. -/
theorem exists_conditionalPairingBox_iff_dominates {D : WeightedDesign m 3}
    (hheavy : AllHeavy D) {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    (∃ paramFirst paramSecond : ℝ, paramFirst * paramSecond ≤ 1
        ∧ 0 ≤ pairMinor D pivot pairFirst ∧ 0 ≤ pairMinor D pivot pairSecond
        ∧ |conditionalPairing D pivot pairFirst pairSecond|
            ≤ paramFirst * pairMinor D pivot pairFirst
        ∧ |conditionalPairing D pivot pairFirst pairSecond|
            ≤ paramSecond * pairMinor D pivot pairSecond)
      ↔ Dominates D {pivot, pairFirst, pairSecond} := by
  constructor
  · rintro ⟨paramFirst, paramSecond, hparamProduct, hminorFirst, hminorSecond,
      hboundFirst, hboundSecond⟩
    exact dominates_of_conditionalPairingBox D hpivotFirst hpivotSecond hpairDistinct
      (hheavy pivot) hparamProduct hminorFirst hminorSecond hboundFirst hboundSecond
  · intro hdominates
    have hpivotPos : 0 < heavyExcess D pivot := allHeavy_heavyExcess_pos hheavy pivot
    have hminorFirst : 0 ≤ pairMinor D pivot pairFirst :=
      pairMinor_nonneg_of_dominates D hpivotFirst hpivotSecond hpairDistinct
        (hheavy pivot) hdominates
    have hminorSecond : 0 ≤ pairMinor D pivot pairSecond := by
      refine pairMinor_nonneg_of_dominates D hpivotSecond hpivotFirst hpairDistinct.symm
        (hheavy pivot) ?_
      rw [Finset.pair_comm pairSecond pairFirst]
      exact hdominates
    have htie : 0 ≤ discriminantTie D pivot pairFirst pairSecond :=
      ((dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
        (hheavy pivot)).mp hdominates).2
    have hsquareLe : conditionalPairing D pivot pairFirst pairSecond ^ 2
        ≤ pairMinor D pivot pairFirst * pairMinor D pivot pairSecond := by
      have hscaled : 0 ≤ heavyExcess D pivot
          * discriminantTie D pivot pairFirst pairSecond := mul_nonneg hpivotPos.le htie
      rw [heavyExcess_mul_discriminantTie_eq] at hscaled
      linarith
    rcases eq_or_lt_of_le hminorFirst with hfirstZero | hfirstPos
    · -- a vanishing minor forces a vanishing conditional pairing
      have hsquareZero : conditionalPairing D pivot pairFirst pairSecond ^ 2 ≤ 0 := by
        rw [← hfirstZero] at hsquareLe
        linarith [hsquareLe]
      have habsZero : |conditionalPairing D pivot pairFirst pairSecond| = 0 := by
        have hzero : conditionalPairing D pivot pairFirst pairSecond = 0 := by
          nlinarith [sq_nonneg (conditionalPairing D pivot pairFirst pairSecond)]
        rw [hzero, abs_zero]
      exact ⟨0, 0, by norm_num, hminorFirst, hminorSecond,
        by rw [habsZero]; simp, by rw [habsZero]; simp⟩
    rcases eq_or_lt_of_le hminorSecond with hsecondZero | hsecondPos
    · have hsquareZero : conditionalPairing D pivot pairFirst pairSecond ^ 2 ≤ 0 := by
        rw [← hsecondZero] at hsquareLe
        linarith [hsquareLe]
      have habsZero : |conditionalPairing D pivot pairFirst pairSecond| = 0 := by
        have hzero : conditionalPairing D pivot pairFirst pairSecond = 0 := by
          nlinarith [sq_nonneg (conditionalPairing D pivot pairFirst pairSecond)]
        rw [hzero, abs_zero]
      exact ⟨0, 0, by norm_num, hminorFirst, hminorSecond,
        by rw [habsZero]; simp, by rw [habsZero]; simp⟩
    refine ⟨|conditionalPairing D pivot pairFirst pairSecond| / pairMinor D pivot pairFirst,
      |conditionalPairing D pivot pairFirst pairSecond| / pairMinor D pivot pairSecond,
      ?_, hminorFirst, hminorSecond, ?_, ?_⟩
    · rw [div_mul_div_comm, div_le_one (mul_pos hfirstPos hsecondPos)]
      rw [← sq_abs (conditionalPairing D pivot pairFirst pairSecond)] at hsquareLe
      nlinarith [hsquareLe]
    · rw [div_mul_cancel₀ _ (ne_of_gt hfirstPos)]
    · rw [div_mul_cancel₀ _ (ne_of_gt hsecondPos)]

/-! ### Cell A as a `DecisionCell`, and its discharge -/

/-- The conditional-pairing box as a `DecisionCell` of
`Gtz.Quantitative.DecisionAtlasSevenThree`: SIX sign conditions, each of degree two in
the triple's six Gram scalars, with rational coefficients once the two parameters are
rational. Six rather than four because each of the two absolute-value bounds is split
into its two linear readings, so that every condition is a polynomial. -/
noncomputable def conditionalPairingBoxCell (paramFirst paramSecond : ℝ)
    (pivot pairFirst pairSecond : Fin m) (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    DecisionCell m where
  signConditions :=
    [fun D => pairMinor D pivot pairFirst,
     fun D => pairMinor D pivot pairSecond,
     fun D => paramFirst * pairMinor D pivot pairFirst
        - conditionalPairing D pivot pairFirst pairSecond,
     fun D => paramFirst * pairMinor D pivot pairFirst
        + conditionalPairing D pivot pairFirst pairSecond,
     fun D => paramSecond * pairMinor D pivot pairSecond
        - conditionalPairing D pivot pairFirst pairSecond,
     fun D => paramSecond * pairMinor D pivot pairSecond
        + conditionalPairing D pivot pairFirst pairSecond]
  pivot := pivot
  pairFirst := pairFirst
  pairSecond := pairSecond
  pivotNePairFirst := hpivotFirst
  pivotNePairSecond := hpivotSecond
  pairFirstNePairSecond := hpairDistinct

theorem isInCell_conditionalPairingBoxCell_iff (D : WeightedDesign m 3)
    (paramFirst paramSecond : ℝ) {pivot pairFirst pairSecond : Fin m}
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    IsInCell (conditionalPairingBoxCell paramFirst paramSecond pivot pairFirst pairSecond
        hpivotFirst hpivotSecond hpairDistinct) D
      ↔ (0 ≤ pairMinor D pivot pairFirst ∧ 0 ≤ pairMinor D pivot pairSecond
          ∧ |conditionalPairing D pivot pairFirst pairSecond|
              ≤ paramFirst * pairMinor D pivot pairFirst
          ∧ |conditionalPairing D pivot pairFirst pairSecond|
              ≤ paramSecond * pairMinor D pivot pairSecond) := by
  constructor
  · intro hinCell
    simp only [IsInCell, conditionalPairingBoxCell, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq] at hinCell
    obtain ⟨hminorFirst, hminorSecond, hfirstUpper, hfirstLower, hsecondUpper,
      hsecondLower⟩ := hinCell
    exact ⟨hminorFirst, hminorSecond, abs_le.mpr ⟨by linarith, by linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · rintro ⟨hminorFirst, hminorSecond, hboundFirst, hboundSecond⟩
    obtain ⟨hfirstLower, hfirstUpper⟩ := abs_le.mp hboundFirst
    obtain ⟨hsecondLower, hsecondUpper⟩ := abs_le.mp hboundSecond
    simp only [IsInCell, conditionalPairingBoxCell, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hminorFirst, hminorSecond, by linarith, by linarith, by linarith, by linarith⟩

/-- **THE CELL OBLIGATION, DISCHARGED**, for every parameter pair whose product is at
most one and every assigned triple of distinct atoms. With this the family plugs
straight into `discriminantCovering_of_atlas`; what no theorem here supplies is
COVERAGE. -/
theorem doesCellDischarge_conditionalPairingBoxCell {paramFirst paramSecond : ℝ}
    (hparamProduct : paramFirst * paramSecond ≤ 1)
    (pivot pairFirst pairSecond : Fin m) (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    DoesCellDischarge (conditionalPairingBoxCell paramFirst paramSecond pivot pairFirst
      pairSecond hpivotFirst hpivotSecond hpairDistinct) := by
  intro D hheavy hinCell
  obtain ⟨hminorFirst, hminorSecond, hboundFirst, hboundSecond⟩ :=
    (isInCell_conditionalPairingBoxCell_iff D paramFirst paramSecond hpivotFirst
      hpivotSecond hpairDistinct).mp hinCell
  exact (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
    (hheavy pivot)).mp
      (dominates_of_conditionalPairingBox D hpivotFirst hpivotSecond hpairDistinct
        (hheavy pivot) hparamProduct hminorFirst hminorSecond hboundFirst hboundSecond)

/-! ### Cell B: the pairing-floor cell, three linear bounds instead of a product bound -/

/-- **THE PAIRING-FLOOR CELL.** A triple whose two pivot minors are nonnegative, whose
three pairings are all at least a common nonnegative floor, and whose sign-blind gap
overshoots by at most twice the floor CUBED, dominates.

This is the product-floor cell of `Gtz.Quantitative.SignReadingCell` with its
degree-three hypothesis on the oriented product replaced by three DEGREE-ONE bounds on
the pairings themselves: `floor ≤ p` on each edge forces
`floor³ ≤ p_pa p_pb p_ab` without ever naming the product. The trade is a genuine
restriction — a triple with one small and two large pairings has a large product and a
small floor — and a genuine simplification: the sign of the product is not assumed, it
is derived from three edge inequalities a search can enumerate. -/
theorem dominates_of_pairingFloor (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hpivotHeavy : 1 < leverageOf (D.atom pivot))
    {pairingFloor : ℝ} (hfloorNonneg : 0 ≤ pairingFloor)
    (hminorFirst : 0 ≤ pairMinor D pivot pairFirst)
    (hminorSecond : 0 ≤ pairMinor D pivot pairSecond)
    (hfloorPivotFirst : pairingFloor ≤ atomPairing D pivot pairFirst)
    (hfloorPivotSecond : pairingFloor ≤ atomPairing D pivot pairSecond)
    (hfloorPair : pairingFloor ≤ atomPairing D pairFirst pairSecond)
    (hgap : -(2 * pairingFloor ^ 3) ≤ excessGap D pivot pairFirst pairSecond) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  have hproductFloor : pairingFloor ^ 3
      ≤ atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond := by
    have hpairStep : pairingFloor * pairingFloor
        ≤ atomPairing D pivot pairFirst * atomPairing D pivot pairSecond :=
      mul_le_mul hfloorPivotFirst hfloorPivotSecond hfloorNonneg
        (le_trans hfloorNonneg hfloorPivotFirst)
    have hcubeStep : (pairingFloor * pairingFloor) * pairingFloor
        ≤ (atomPairing D pivot pairFirst * atomPairing D pivot pairSecond)
          * atomPairing D pairFirst pairSecond :=
      mul_le_mul hpairStep hfloorPair hfloorNonneg
        (le_trans (mul_nonneg hfloorNonneg hfloorNonneg) hpairStep)
    nlinarith [hcubeStep]
  refine (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
    hpairDistinct hpivotHeavy).mpr ⟨?_, ?_⟩
  · rw [discriminantTrace_eq_pairMinor_add]
    linarith
  · rw [discriminantTie_eq_excessGap_add_tripleProduct]
    linarith

/-- The pairing-floor cell as a `DecisionCell`: six sign conditions — the three edge
bounds of degree one, the two pivot minors of degree two, and the relaxed gap of degree
three. So the gap condition keeps the degree of the leg it relaxes. -/
noncomputable def pairingFloorCell (pairingFloor : ℝ)
    (pivot pairFirst pairSecond : Fin m) (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    DecisionCell m where
  signConditions :=
    [fun D => pairMinor D pivot pairFirst,
     fun D => pairMinor D pivot pairSecond,
     fun D => atomPairing D pivot pairFirst - pairingFloor,
     fun D => atomPairing D pivot pairSecond - pairingFloor,
     fun D => atomPairing D pairFirst pairSecond - pairingFloor,
     fun D => excessGap D pivot pairFirst pairSecond + 2 * pairingFloor ^ 3]
  pivot := pivot
  pairFirst := pairFirst
  pairSecond := pairSecond
  pivotNePairFirst := hpivotFirst
  pivotNePairSecond := hpivotSecond
  pairFirstNePairSecond := hpairDistinct

theorem isInCell_pairingFloorCell_iff (D : WeightedDesign m 3) (pairingFloor : ℝ)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    IsInCell (pairingFloorCell pairingFloor pivot pairFirst pairSecond hpivotFirst
        hpivotSecond hpairDistinct) D
      ↔ (0 ≤ pairMinor D pivot pairFirst ∧ 0 ≤ pairMinor D pivot pairSecond
          ∧ pairingFloor ≤ atomPairing D pivot pairFirst
          ∧ pairingFloor ≤ atomPairing D pivot pairSecond
          ∧ pairingFloor ≤ atomPairing D pairFirst pairSecond
          ∧ -(2 * pairingFloor ^ 3) ≤ excessGap D pivot pairFirst pairSecond) := by
  constructor
  · intro hinCell
    simp only [IsInCell, pairingFloorCell, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hinCell
    obtain ⟨hminorFirst, hminorSecond, hfloorFirst, hfloorSecond, hfloorPair, hgap⟩ :=
      hinCell
    exact ⟨hminorFirst, hminorSecond, by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨hminorFirst, hminorSecond, hfloorFirst, hfloorSecond, hfloorPair, hgap⟩
    simp only [IsInCell, pairingFloorCell, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq]
    exact ⟨hminorFirst, hminorSecond, by linarith, by linarith, by linarith, by linarith⟩

theorem doesCellDischarge_pairingFloorCell {pairingFloor : ℝ}
    (hfloorNonneg : 0 ≤ pairingFloor) (pivot pairFirst pairSecond : Fin m)
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    DoesCellDischarge (pairingFloorCell pairingFloor pivot pairFirst pairSecond
      hpivotFirst hpivotSecond hpairDistinct) := by
  intro D hheavy hinCell
  obtain ⟨hminorFirst, hminorSecond, hfloorFirst, hfloorSecond, hfloorPair, hgap⟩ :=
    (isInCell_pairingFloorCell_iff D pairingFloor hpivotFirst hpivotSecond
      hpairDistinct).mp hinCell
  exact (dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
    (hheavy pivot)).mp
      (dominates_of_pairingFloor D hpivotFirst hpivotSecond hpairDistinct (hheavy pivot)
        hfloorNonneg hminorFirst hminorSecond hfloorFirst hfloorSecond hfloorPair hgap)

/-! ### The shipped product-floor family is exactly complete too -/

/-- **THE PRODUCT-FLOOR FAMILY IS EXACTLY COMPLETE AT EVERY TRIPLE.** At a triple of
distinct atoms of an all-heavy design, domination is EQUIVALENT to the existence of a
product floor putting the triple in `Gtz.productFloorCell`. The witness is the exact
ratio `productFloor = (p_pa p_pb p_ab) / (u_p u_a u_b)`, at which the third hypothesis
holds with equality and the fourth is the tie leg verbatim.

This upgrades the honest caveat of `Gtz.Quantitative.SignReadingCell` — "no atlas built
from this family is proved to cover" — into a sharp localisation: the family loses
NOTHING per triple, so the whole residue of the atlas programme is the choice of TRIPLE
and of PARAMETER, never the shape of the certificate. No new cell family can enlarge
the per-triple reach. -/
theorem exists_productFloor_iff_dominates {D : WeightedDesign m 3} (hheavy : AllHeavy D)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond) :
    (∃ productFloor : ℝ, 0 ≤ pairMinor D pivot pairFirst
        ∧ 0 ≤ pairMinor D pivot pairSecond
        ∧ productFloor * (heavyExcess D pivot * heavyExcess D pairFirst
              * heavyExcess D pairSecond)
            ≤ atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
              * atomPairing D pairFirst pairSecond
        ∧ heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
              + heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
              + heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2
            ≤ (1 + 2 * productFloor) * (heavyExcess D pivot * heavyExcess D pairFirst
              * heavyExcess D pairSecond))
      ↔ Dominates D {pivot, pairFirst, pairSecond} := by
  have hpivotPos : 0 < heavyExcess D pivot := allHeavy_heavyExcess_pos hheavy pivot
  have hfirstPos : 0 < heavyExcess D pairFirst := allHeavy_heavyExcess_pos hheavy pairFirst
  have hsecondPos : 0 < heavyExcess D pairSecond :=
    allHeavy_heavyExcess_pos hheavy pairSecond
  have hexcessProductPos : 0 < heavyExcess D pivot * heavyExcess D pairFirst
      * heavyExcess D pairSecond := mul_pos (mul_pos hpivotPos hfirstPos) hsecondPos
  constructor
  · rintro ⟨productFloor, hminorFirst, hminorSecond, hproduct, hrelaxed⟩
    exact dominates_of_productFloor D hpivotFirst hpivotSecond hpairDistinct
      (hheavy pivot) (productFloor := productFloor) hminorFirst hminorSecond hproduct
      hrelaxed
  · intro hdominates
    have hminorFirst : 0 ≤ pairMinor D pivot pairFirst :=
      pairMinor_nonneg_of_dominates D hpivotFirst hpivotSecond hpairDistinct
        (hheavy pivot) hdominates
    have hminorSecond : 0 ≤ pairMinor D pivot pairSecond := by
      refine pairMinor_nonneg_of_dominates D hpivotSecond hpivotFirst hpairDistinct.symm
        (hheavy pivot) ?_
      rw [Finset.pair_comm pairSecond pairFirst]
      exact hdominates
    have htie : 0 ≤ discriminantTie D pivot pairFirst pairSecond :=
      ((dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond hpairDistinct
        (hheavy pivot)).mp hdominates).2
    rw [discriminantTie_eq_excessGap_add_tripleProduct, excessGap] at htie
    refine ⟨(atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond)
      / (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond),
      hminorFirst, hminorSecond, ?_, ?_⟩
    · rw [div_mul_cancel₀ _ (ne_of_gt hexcessProductPos)]
    · have hcancel : atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
              * atomPairing D pairFirst pairSecond
            / (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond)
            * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond)
          = atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
              * atomPairing D pairFirst pairSecond :=
        div_mul_cancel₀ _ (ne_of_gt hexcessProductPos)
      have hexpand : (1 + 2 * (atomPairing D pivot pairFirst
                * atomPairing D pivot pairSecond * atomPairing D pairFirst pairSecond
              / (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond)))
              * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond)
            = heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond
              + 2 * (atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
                * atomPairing D pairFirst pairSecond) := by
        linear_combination 2 * hcancel
      rw [hexpand]
      linarith

/-! ### The covering, reframed twice: only the triple is left -/

/-- **RANK THREE IS A COVERING BY DEGREE-TWO CELLS.** `DiscriminantCovering m` is
equivalent to: every all-heavy weighted `(m,3)` design owns a triple and two parameters
of product at most one at which the four conditional-pairing box inequalities hold. Both
legs of the discriminant system — degrees two and three in the Gram entries — are
replaced by four inequalities of degree TWO, with no loss.

What this does NOT do: it supplies no coverage, and the parameters are real. It moves
the whole difficulty into the two choices — which triple, and which parameters — and
records that the certificate SHAPE is no longer where the difficulty lives. -/
theorem discriminantCovering_iff_conditionalPairingCovering (size : ℕ) :
    DiscriminantCovering size
      ↔ ∀ D : WeightedDesign size 3, AllHeavy D →
          ∃ (pivot pairFirst pairSecond : Fin size) (paramFirst paramSecond : ℝ),
            pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
              ∧ paramFirst * paramSecond ≤ 1
              ∧ 0 ≤ pairMinor D pivot pairFirst ∧ 0 ≤ pairMinor D pivot pairSecond
              ∧ |conditionalPairing D pivot pairFirst pairSecond|
                  ≤ paramFirst * pairMinor D pivot pairFirst
              ∧ |conditionalPairing D pivot pairFirst pairSecond|
                  ≤ paramSecond * pairMinor D pivot pairSecond := by
  constructor
  · intro hcover D hheavy
    obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
      htrace, htie⟩ := hcover D hheavy
    obtain ⟨paramFirst, paramSecond, hparamProduct, hminorFirst, hminorSecond,
      hboundFirst, hboundSecond⟩ :=
      (exists_conditionalPairingBox_iff_dominates hheavy hpivotFirst hpivotSecond
        hpairDistinct).mpr
        ((dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
          hpairDistinct (hheavy pivot)).mpr ⟨htrace, htie⟩)
    exact ⟨pivot, pairFirst, pairSecond, paramFirst, paramSecond, hpivotFirst,
      hpivotSecond, hpairDistinct, hparamProduct, hminorFirst, hminorSecond,
      hboundFirst, hboundSecond⟩
  · intro hbox D hheavy
    obtain ⟨pivot, pairFirst, pairSecond, paramFirst, paramSecond, hpivotFirst,
      hpivotSecond, hpairDistinct, hparamProduct, hminorFirst, hminorSecond,
      hboundFirst, hboundSecond⟩ := hbox D hheavy
    refine ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct, ?_, ?_⟩
    · exact ((dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
        hpairDistinct (hheavy pivot)).mp
          (dominates_of_conditionalPairingBox D hpivotFirst hpivotSecond hpairDistinct
            (hheavy pivot) hparamProduct hminorFirst hminorSecond hboundFirst
            hboundSecond)).1
    · exact ((dominates_triple_iff_discriminantSystem D hpivotFirst hpivotSecond
        hpairDistinct (hheavy pivot)).mp
          (dominates_of_conditionalPairingBox D hpivotFirst hpivotSecond hpairDistinct
            (hheavy pivot) hparamProduct hminorFirst hminorSecond hboundFirst
            hboundSecond)).2

/-- **THE FRONTIER, AS A DEGREE-TWO COVERING.** GTZ at rank three for every `n` is the
existence, at every all-heavy weighted `(7,3)` design, of one of `35` triples and two
real parameters of product at most one satisfying four degree-two inequalities in the
triple's six Gram scalars. -/
theorem conditionalPairingCovering_seven_iff_rank_three :
    (∀ D : WeightedDesign 7 3, AllHeavy D →
        ∃ (pivot pairFirst pairSecond : Fin 7) (paramFirst paramSecond : ℝ),
          pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ paramFirst * paramSecond ≤ 1
            ∧ 0 ≤ pairMinor D pivot pairFirst ∧ 0 ≤ pairMinor D pivot pairSecond
            ∧ |conditionalPairing D pivot pairFirst pairSecond|
                ≤ paramFirst * pairMinor D pivot pairFirst
            ∧ |conditionalPairing D pivot pairFirst pairSecond|
                ≤ paramSecond * pairMinor D pivot pairSecond)
      ↔ GtzWeightedAll 3 :=
  (discriminantCovering_iff_conditionalPairingCovering 7).symm.trans
    discriminantCovering_seven_iff_rank_three

/-! ### The graphic design of `K4`, exactly: the campaign's named residue object -/

/-- The six edges of `K4` as vectors in `R³`: the three coordinate-plane diagonals and
their reflections. Every vector has squared length `2`, the three pairs
`{0,1}, {2,3}, {4,5}` are orthogonal (the three perfect matchings of `K4`), and every
other pair has inner product `±1` — exactly the `M(K4)` pattern. -/
def kFourEdgeVector : Fin 6 → Fin 3 → ℝ :=
  ![![1, 1, 0], ![1, -1, 0], ![1, 0, 1], ![1, 0, -1], ![0, 1, 1], ![0, 1, -1]]

/-- The scale making every leverage exactly `3`: `sqrt 6 / 2`, whose square is `3/2`.
The atom entries are irrational but every quantity the design is used for — Parseval,
leverages, pairings — depends only on the SQUARE, so all of them are exact rationals. -/
noncomputable def graphicKFourScale : ℝ := Real.sqrt 6 / 2

theorem graphicKFourScale_mul_self : graphicKFourScale * graphicKFourScale = 3 / 2 :=
  calc graphicKFourScale * graphicKFourScale = Real.sqrt 6 * Real.sqrt 6 / 4 := by
        rw [graphicKFourScale]; ring
    _ = 6 / 4 := by rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    _ = 3 / 2 := by norm_num

theorem graphicKFourScale_sq : graphicKFourScale ^ 2 = 3 / 2 := by
  rw [pow_two]; exact graphicKFourScale_mul_self

noncomputable def graphicKFourAtom (edge : Fin 6) : Fin 3 → ℝ :=
  fun coord => graphicKFourScale * kFourEdgeVector edge coord

theorem atomMatrix_graphicKFourAtom_apply (edge : Fin 6) (rowIndex colIndex : Fin 3) :
    atomMatrix (graphicKFourAtom edge) rowIndex colIndex
      = 3 / 2 * (kFourEdgeVector edge rowIndex * kFourEdgeVector edge colIndex) := by
  simp only [atomMatrix, Matrix.vecMulVec_apply, graphicKFourAtom]
  linear_combination (kFourEdgeVector edge rowIndex * kFourEdgeVector edge colIndex)
    * graphicKFourScale_mul_self

/-- **The graphic `(6,3)` design of `K4`**, exactly rational in every quantity that
matters: six atoms of leverage exactly `3`, Gram off-diagonal in `{0, ±3/2}`, uniform
weight `1/6`. This is catalogue class `simple_n06_r03_#5`, the campaign's `q6m8`, and
the object `Gtz.Quantitative.SignReadingCell` records as carrying the surviving residue
of the shipped cell library. -/
noncomputable def graphicKFourDesign : WeightedDesign 6 3 where
  atom := graphicKFourAtom
  weight := fun _ => 1 / 6
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_six,
      atomMatrix_graphicKFourAtom_apply]
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [kFourEdgeVector] <;> norm_num

theorem graphicKFourDesign_atom (edge : Fin 6) :
    graphicKFourDesign.atom edge = graphicKFourAtom edge := rfl

/-- Every leverage is exactly `3`: `(3/2) · 2`. -/
theorem graphicKFourDesign_leverage (edge : Fin 6) :
    leverageOf (graphicKFourDesign.atom edge) = 3 := by
  have hsquare : ∀ coord : Fin 3, graphicKFourAtom edge coord ^ 2
      = 3 / 2 * kFourEdgeVector edge coord ^ 2 := by
    intro coord
    rw [graphicKFourAtom, mul_pow, graphicKFourScale_sq]
  rw [graphicKFourDesign_atom]
  simp only [leverageOf, Fin.sum_univ_three, hsquare]
  fin_cases edge <;> simp [kFourEdgeVector]

theorem graphicKFourDesign_allHeavy : AllHeavy graphicKFourDesign := by
  intro edge
  rw [graphicKFourDesign_leverage]
  norm_num

theorem graphicKFourDesign_heavyExcess (edge : Fin 6) :
    heavyExcess graphicKFourDesign edge = 2 := by
  rw [heavyExcess, graphicKFourDesign_leverage]
  norm_num

theorem graphicKFourDesign_atomPairing (edgeFirst edgeSecond : Fin 6) :
    atomPairing graphicKFourDesign edgeFirst edgeSecond
      = 3 / 2 * ∑ coord, kFourEdgeVector edgeFirst coord * kFourEdgeVector edgeSecond coord := by
  rw [atomPairing, graphicKFourDesign_atom, graphicKFourDesign_atom, dotProduct,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun coord _ => ?_
  simp only [graphicKFourAtom]
  linear_combination (kFourEdgeVector edgeFirst coord * kFourEdgeVector edgeSecond coord)
    * graphicKFourScale_mul_self

/-! #### The star triple at the first vertex

`{0, 2, 4}` carries the three edges `(1,1,0)`, `(1,0,1)`, `(0,1,1)` — a STAR of `K4`,
three edges through one vertex — so all three pairings are `+3/2` and the oriented
product is `+27/8`.

The full triple census is a CROSS-CHECK, not a theorem in this file: of the twenty
triples, the four STARS `{0,2,4}, {0,3,5}, {1,2,5}, {1,3,4}` are exactly the dominating
ones (tie `+5/4`), the four TRIANGLES have product `−27/8` and tie `−49/4`, and the
twelve triples containing a perfect-matching pair have product `0` and tie `−1`. Only
the star `{0,2,4}` is discharged below by the kernel. -/

theorem graphicKFourDesign_atomPairing_zeroTwo :
    atomPairing graphicKFourDesign 0 2 = 3 / 2 := by
  rw [graphicKFourDesign_atomPairing]
  simp [kFourEdgeVector, Fin.sum_univ_three]

theorem graphicKFourDesign_atomPairing_zeroFour :
    atomPairing graphicKFourDesign 0 4 = 3 / 2 := by
  rw [graphicKFourDesign_atomPairing]
  simp [kFourEdgeVector, Fin.sum_univ_three]

theorem graphicKFourDesign_atomPairing_twoFour :
    atomPairing graphicKFourDesign 2 4 = 3 / 2 := by
  rw [graphicKFourDesign_atomPairing]
  simp [kFourEdgeVector, Fin.sum_univ_three]

theorem graphicKFourDesign_pairMinor_zeroTwo :
    pairMinor graphicKFourDesign 0 2 = 7 / 4 := by
  rw [pairMinor, graphicKFourDesign_heavyExcess, graphicKFourDesign_heavyExcess,
    graphicKFourDesign_atomPairing_zeroTwo]
  norm_num

theorem graphicKFourDesign_pairMinor_zeroFour :
    pairMinor graphicKFourDesign 0 4 = 7 / 4 := by
  rw [pairMinor, graphicKFourDesign_heavyExcess, graphicKFourDesign_heavyExcess,
    graphicKFourDesign_atomPairing_zeroFour]
  norm_num

/-- The sign-blind gap of the star triple is `−11/2`: the design sits strictly OUTSIDE
the sign-blind body, by `27/4 − (−11/2) = 49/4`. -/
theorem graphicKFourDesign_excessGap_starTriple :
    excessGap graphicKFourDesign 0 2 4 = -(11 / 2) := by
  rw [excessGap, graphicKFourDesign_heavyExcess, graphicKFourDesign_heavyExcess,
    graphicKFourDesign_heavyExcess, graphicKFourDesign_atomPairing_zeroTwo,
    graphicKFourDesign_atomPairing_zeroFour, graphicKFourDesign_atomPairing_twoFour]
  norm_num

/-- The tie leg of the star triple is `+5/4`, strictly positive: the star triple
dominates with margin, so this design is NOT a counterexample to anything. -/
theorem graphicKFourDesign_discriminantTie_starTriple :
    discriminantTie graphicKFourDesign 0 2 4 = 5 / 4 := by
  rw [discriminantTie_eq_excessGap_add_tripleProduct,
    graphicKFourDesign_excessGap_starTriple, graphicKFourDesign_atomPairing_zeroTwo,
    graphicKFourDesign_atomPairing_zeroFour, graphicKFourDesign_atomPairing_twoFour]
  norm_num

/-! ### The refutation: a shipped cell DOES fire at the K4 residue -/

/-- **THE RECORDED RESIDUE CLAIM IS FALSE, AND THE PRODUCT-FLOOR CELL IS WHAT REFUTES
IT.** `Gtz.Quantitative.SignReadingCell` records, in prose, that the surviving residue
of the shipped cell library "survives at exactly rational points — the `(6,3)` graphic
design of `K4` and its `(7,3)` atom split have every leverage `3`, Gram entries in
`{3, ±3/2, 0}`, strictly dominating triples, and NO SHIPPED CELL FIRING AT ANY TRIPLE."
The last clause is false. At the star triple `{0,2,4}` of that very design the shipped
`Gtz.productFloorCell` fires at `productFloor = 3/8` — a value ON the rational grid
`{1/8, 1/4, 3/8}` the same file reports measuring — because all four of its sign
conditions hold:

  `pairMinor 0 2 = 7/4 ≥ 0`,  `pairMinor 0 4 = 7/4 ≥ 0`,
  `(3/8)·8 = 3 ≤ 27/8 = p_02 p_04 p_24`,
  `27/2 ≤ (1 + 3/4)·8 = 14`.

The rest of the recorded claim is CONFIRMED below: the sign-blind, coherent-sign and
two-moment families all fail at this triple. So the correct statement is that the
residue survives against three of the four shipped families, not all four. -/
theorem isInCell_productFloorCell_threeEighths_graphicKFour :
    IsInCell (productFloorCell (3 / 8) (0 : Fin 6) 2 4
        (by decide) (by decide) (by decide))
      graphicKFourDesign := by
  refine (isInCell_productFloorCell_iff graphicKFourDesign (3 / 8)
    (by decide) (by decide) (by decide)).mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [graphicKFourDesign_pairMinor_zeroTwo]; norm_num
  · rw [graphicKFourDesign_pairMinor_zeroFour]; norm_num
  · rw [graphicKFourDesign_heavyExcess, graphicKFourDesign_heavyExcess,
      graphicKFourDesign_heavyExcess, graphicKFourDesign_atomPairing_zeroTwo,
      graphicKFourDesign_atomPairing_zeroFour, graphicKFourDesign_atomPairing_twoFour]
    norm_num
  · rw [graphicKFourDesign_heavyExcess, graphicKFourDesign_heavyExcess,
      graphicKFourDesign_heavyExcess, graphicKFourDesign_atomPairing_zeroTwo,
      graphicKFourDesign_atomPairing_zeroFour, graphicKFourDesign_atomPairing_twoFour]
    norm_num

/-- **The exact admissible window for the product floor at the K4 star**:
`11/32 ≤ productFloor ≤ 27/64`. The lower end is forced by the relaxed aggregate, the
upper end by the oriented product, and the shipped grid value `3/8 = 24/64` sits inside
with room on both sides — so the refutation above is not a knife-edge coincidence. -/
theorem graphicKFour_productFloor_window (productFloor : ℝ) :
    (productFloor * (heavyExcess graphicKFourDesign 0 * heavyExcess graphicKFourDesign 2
          * heavyExcess graphicKFourDesign 4)
        ≤ atomPairing graphicKFourDesign 0 2 * atomPairing graphicKFourDesign 0 4
          * atomPairing graphicKFourDesign 2 4
      ∧ heavyExcess graphicKFourDesign 4 * atomPairing graphicKFourDesign 0 2 ^ 2
            + heavyExcess graphicKFourDesign 2 * atomPairing graphicKFourDesign 0 4 ^ 2
            + heavyExcess graphicKFourDesign 0 * atomPairing graphicKFourDesign 2 4 ^ 2
          ≤ (1 + 2 * productFloor)
            * (heavyExcess graphicKFourDesign 0 * heavyExcess graphicKFourDesign 2
              * heavyExcess graphicKFourDesign 4))
      ↔ (11 / 32 ≤ productFloor ∧ productFloor ≤ 27 / 64) := by
  rw [graphicKFourDesign_heavyExcess, graphicKFourDesign_heavyExcess,
    graphicKFourDesign_heavyExcess, graphicKFourDesign_atomPairing_zeroTwo,
    graphicKFourDesign_atomPairing_zeroFour, graphicKFourDesign_atomPairing_twoFour]
  constructor
  · rintro ⟨hproduct, hrelaxed⟩
    exact ⟨by nlinarith [hrelaxed], by nlinarith [hproduct]⟩
  · rintro ⟨hlower, hupper⟩
    exact ⟨by nlinarith [hupper], by nlinarith [hlower]⟩

/-- The star triple dominates, through the shipped product-floor cell. -/
theorem graphicKFourDesign_dominates_starTriple :
    Dominates graphicKFourDesign {0, 2, 4} := by
  refine dominates_of_productFloor graphicKFourDesign (by decide) (by decide) (by decide)
    (by rw [graphicKFourDesign_leverage]; norm_num) (productFloor := 3 / 8) ?_ ?_ ?_ ?_
  · rw [graphicKFourDesign_pairMinor_zeroTwo]; norm_num
  · rw [graphicKFourDesign_pairMinor_zeroFour]; norm_num
  · exact ((graphicKFour_productFloor_window (3 / 8)).mpr ⟨by norm_num, by norm_num⟩).1
  · exact ((graphicKFour_productFloor_window (3 / 8)).mpr ⟨by norm_num, by norm_num⟩).2

/-! ### The confirmed half: three of the four shipped families really do fail -/

/-- The star triple is NOT sign-blind-good: `2·|27/8| = 27/4` against a gap of `−11/2`.
So the radius-box family, the symmetric box and the ball — all inside the sign-blind
closure — miss this triple, exactly as recorded. -/
theorem not_isSignBlindGoodTriple_graphicKFour_starTriple :
    ¬ IsSignBlindGoodTriple graphicKFourDesign 0 2 4 := by
  rw [IsSignBlindGoodTriple, graphicKFourDesign_excessGap_starTriple,
    graphicKFourDesign_atomPairing_zeroTwo, graphicKFourDesign_atomPairing_zeroFour,
    graphicKFourDesign_atomPairing_twoFour]
  norm_num [abs_of_nonneg]

/-- The star triple fails the coherent-sign cell's aggregate hypothesis: the sign-blind
gap is `−11/2 < 0`, and that hypothesis is `0 ≤ excessGap` term for term. -/
theorem graphicKFour_starTriple_excessGap_neg :
    excessGap graphicKFourDesign 0 2 4 < 0 := by
  rw [graphicKFourDesign_excessGap_starTriple]; norm_num

/-- The star triple fails the two-moment certificate: the gap is exactly `−10`. -/
theorem graphicKFour_starTriple_twoMomentGap :
    twoMomentGap (leverageOf (graphicKFourDesign.atom 0))
        (leverageOf (graphicKFourDesign.atom 2)) (leverageOf (graphicKFourDesign.atom 4))
        (atomPairing graphicKFourDesign 0 2) (atomPairing graphicKFourDesign 0 4)
        (atomPairing graphicKFourDesign 2 4) = -10 := by
  rw [graphicKFourDesign_leverage, graphicKFourDesign_leverage, graphicKFourDesign_leverage,
    graphicKFourDesign_atomPairing_zeroTwo, graphicKFourDesign_atomPairing_zeroFour,
    graphicKFourDesign_atomPairing_twoFour, twoMomentGap]
  norm_num

/-- **THE WHOLE RADIUS-BOX FAMILY IS CONTAINED IN THE SIGN-BLIND CLOSURE**, as a
theorem. `Gtz.Quantitative.GoodTripleGraph` records the containment — in fact the
equivalence at optimal radii — in prose, and proves it only for the symmetric box
(`isSignBlindGoodTriple_of_isBoxGoodTriangle`). Here it is discharged for every
admissible triple of radii: the three box bounds scale to `r_i² · U`, their product
bounds the oriented product by `r_1 r_2 r_3 · U`, and admissibility sums the four terms
below `U`. This is what turns a sign-blind refutation into a refutation of the entire
radius-box family at a named triple. -/
theorem isSignBlindGoodTriple_of_radiusBox (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) (hpivotPos : 0 < heavyExcess D pivot)
    (hfirstPos : 0 < heavyExcess D pairFirst) (hsecondPos : 0 < heavyExcess D pairSecond)
    {radiusPivotFirst radiusPivotSecond radiusPair : ℝ}
    (hradiusPivotFirstNonneg : 0 ≤ radiusPivotFirst)
    (hradiusPivotSecondNonneg : 0 ≤ radiusPivotSecond)
    (hradiusPairNonneg : 0 ≤ radiusPair)
    (hadmissible : radiusPivotFirst ^ 2 + radiusPivotSecond ^ 2 + radiusPair ^ 2
        + 2 * radiusPivotFirst * radiusPivotSecond * radiusPair ≤ 1)
    (hboxPivotFirst : atomPairing D pivot pairFirst ^ 2
        ≤ radiusPivotFirst ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst))
    (hboxPivotSecond : atomPairing D pivot pairSecond ^ 2
        ≤ radiusPivotSecond ^ 2 * (heavyExcess D pivot * heavyExcess D pairSecond))
    (hboxPair : atomPairing D pairFirst pairSecond ^ 2
        ≤ radiusPair ^ 2 * (heavyExcess D pairFirst * heavyExcess D pairSecond)) :
    IsSignBlindGoodTriple D pivot pairFirst pairSecond := by
  have hexcessProductPos : 0 < heavyExcess D pivot * heavyExcess D pairFirst
      * heavyExcess D pairSecond := mul_pos (mul_pos hpivotPos hfirstPos) hsecondPos
  have hscaledPivotFirst : heavyExcess D pairSecond * atomPairing D pivot pairFirst ^ 2
      ≤ radiusPivotFirst ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst
        * heavyExcess D pairSecond) := by
    nlinarith [mul_le_mul_of_nonneg_left hboxPivotFirst hsecondPos.le]
  have hscaledPivotSecond : heavyExcess D pairFirst * atomPairing D pivot pairSecond ^ 2
      ≤ radiusPivotSecond ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst
        * heavyExcess D pairSecond) := by
    nlinarith [mul_le_mul_of_nonneg_left hboxPivotSecond hfirstPos.le]
  have hscaledPair : heavyExcess D pivot * atomPairing D pairFirst pairSecond ^ 2
      ≤ radiusPair ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst
        * heavyExcess D pairSecond) := by
    nlinarith [mul_le_mul_of_nonneg_left hboxPair hpivotPos.le]
  have hradiusProductNonneg : 0 ≤ radiusPivotFirst * radiusPivotSecond * radiusPair
      * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond) :=
    mul_nonneg (mul_nonneg (mul_nonneg hradiusPivotFirstNonneg hradiusPivotSecondNonneg)
      hradiusPairNonneg) hexcessProductPos.le
  have hcubeBound : (atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond) ^ 2
      ≤ (radiusPivotFirst * radiusPivotSecond * radiusPair
        * (heavyExcess D pivot * heavyExcess D pairFirst
          * heavyExcess D pairSecond)) ^ 2 := by
    have hstep : (atomPairing D pivot pairFirst ^ 2)
          * (atomPairing D pivot pairSecond ^ 2) * (atomPairing D pairFirst pairSecond ^ 2)
        ≤ (radiusPivotFirst ^ 2 * (heavyExcess D pivot * heavyExcess D pairFirst))
          * (radiusPivotSecond ^ 2 * (heavyExcess D pivot * heavyExcess D pairSecond))
          * (radiusPair ^ 2 * (heavyExcess D pairFirst * heavyExcess D pairSecond)) := by
      refine mul_le_mul (mul_le_mul hboxPivotFirst hboxPivotSecond (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (mul_pos hpivotPos hfirstPos).le)) hboxPair
        (sq_nonneg _) ?_
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_pos hpivotPos hfirstPos).le)
        (mul_nonneg (sq_nonneg _) (mul_pos hpivotPos hsecondPos).le)
    nlinarith [hstep]
  have habsBound : |atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
        * atomPairing D pairFirst pairSecond|
      ≤ radiusPivotFirst * radiusPivotSecond * radiusPair
        * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond) := by
    have habsSq : |atomPairing D pivot pairFirst * atomPairing D pivot pairSecond
          * atomPairing D pairFirst pairSecond| ^ 2
        ≤ (radiusPivotFirst * radiusPivotSecond * radiusPair
          * (heavyExcess D pivot * heavyExcess D pairFirst
            * heavyExcess D pairSecond)) ^ 2 := by
      rw [sq_abs]; exact hcubeBound
    nlinarith [habsSq, abs_nonneg (atomPairing D pivot pairFirst
      * atomPairing D pivot pairSecond * atomPairing D pairFirst pairSecond),
      hradiusProductNonneg]
  have hadmissibleScaled : (radiusPivotFirst ^ 2 + radiusPivotSecond ^ 2 + radiusPair ^ 2
        + 2 * radiusPivotFirst * radiusPivotSecond * radiusPair)
      * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond)
      ≤ 1 * (heavyExcess D pivot * heavyExcess D pairFirst * heavyExcess D pairSecond) :=
    mul_le_mul_of_nonneg_right hadmissible hexcessProductPos.le
  rw [IsSignBlindGoodTriple, excessGap]
  nlinarith [hscaledPivotFirst, hscaledPivotSecond, hscaledPair, habsBound,
    hadmissibleScaled]

/-- **NO ADMISSIBLE RADIUS BOX WHATSOEVER CONTAINS THE K4 STAR TRIPLE.** Non-subsumption
of the new cells by the shipped radius-box family, proved rather than asserted: the star
triple fails the sign-blind closure, and every admissible radius box lands inside that
closure. The whole anisotropic family, at every triple of radii, misses this triple. -/
theorem no_radiusBox_at_graphicKFour_starTriple
    {radiusPivotFirst radiusPivotSecond radiusPair : ℝ}
    (hradiusPivotFirstNonneg : 0 ≤ radiusPivotFirst)
    (hradiusPivotSecondNonneg : 0 ≤ radiusPivotSecond)
    (hradiusPairNonneg : 0 ≤ radiusPair)
    (hadmissible : radiusPivotFirst ^ 2 + radiusPivotSecond ^ 2 + radiusPair ^ 2
        + 2 * radiusPivotFirst * radiusPivotSecond * radiusPair ≤ 1) :
    ¬ (atomPairing graphicKFourDesign 0 2 ^ 2
          ≤ radiusPivotFirst ^ 2 * (heavyExcess graphicKFourDesign 0
            * heavyExcess graphicKFourDesign 2)
        ∧ atomPairing graphicKFourDesign 0 4 ^ 2
          ≤ radiusPivotSecond ^ 2 * (heavyExcess graphicKFourDesign 0
            * heavyExcess graphicKFourDesign 4)
        ∧ atomPairing graphicKFourDesign 2 4 ^ 2
          ≤ radiusPair ^ 2 * (heavyExcess graphicKFourDesign 2
            * heavyExcess graphicKFourDesign 4)) := by
  rintro ⟨hboxPivotFirst, hboxPivotSecond, hboxPair⟩
  refine not_isSignBlindGoodTriple_graphicKFour_starTriple ?_
  refine isSignBlindGoodTriple_of_radiusBox graphicKFourDesign 0 2 4 ?_ ?_ ?_
    hradiusPivotFirstNonneg hradiusPivotSecondNonneg hradiusPairNonneg hadmissible
    hboxPivotFirst hboxPivotSecond hboxPair
  · rw [graphicKFourDesign_heavyExcess]; norm_num
  · rw [graphicKFourDesign_heavyExcess]; norm_num
  · rw [graphicKFourDesign_heavyExcess]; norm_num

/-! ### Both new cells fire at the K4 residue as well -/

/-- The conditional pairing of the star triple is `3/4`, well inside both pivot minors
`7/4`, so the UNIT member of the conditional-pairing box — no parameter at all, four
degree-two inequalities — fires at the K4 residue. -/
theorem graphicKFourDesign_conditionalPairing_starTriple :
    conditionalPairing graphicKFourDesign 0 2 4 = 3 / 4 := by
  rw [conditionalPairing, graphicKFourDesign_heavyExcess,
    graphicKFourDesign_atomPairing_zeroTwo, graphicKFourDesign_atomPairing_zeroFour,
    graphicKFourDesign_atomPairing_twoFour]
  norm_num

theorem graphicKFourDesign_dominates_starTriple_of_unitConditionalBox :
    Dominates graphicKFourDesign {0, 2, 4} := by
  refine dominates_of_unitConditionalPairingBox graphicKFourDesign (by decide) (by decide)
    (by decide) (by rw [graphicKFourDesign_leverage]; norm_num) ?_ ?_
  · rw [graphicKFourDesign_conditionalPairing_starTriple,
      graphicKFourDesign_pairMinor_zeroTwo]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    norm_num
  · rw [graphicKFourDesign_conditionalPairing_starTriple,
      graphicKFourDesign_pairMinor_zeroFour]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)]
    norm_num

/-- The pairing-floor cell fires at the K4 residue with floor `3/2`: all three pairings
equal the floor and the gap `−11/2` clears `−2·(3/2)³ = −27/4`. -/
theorem graphicKFourDesign_dominates_starTriple_of_pairingFloor :
    Dominates graphicKFourDesign {0, 2, 4} := by
  refine dominates_of_pairingFloor graphicKFourDesign (by decide) (by decide) (by decide)
    (by rw [graphicKFourDesign_leverage]; norm_num) (pairingFloor := 3 / 2) (by norm_num)
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [graphicKFourDesign_pairMinor_zeroTwo]; norm_num
  · rw [graphicKFourDesign_pairMinor_zeroFour]; norm_num
  · rw [graphicKFourDesign_atomPairing_zeroTwo]
  · rw [graphicKFourDesign_atomPairing_zeroFour]
  · rw [graphicKFourDesign_atomPairing_twoFour]
  · rw [graphicKFourDesign_excessGap_starTriple]; norm_num

/-! ### The refutation at the FRONTIER size, through the atom split -/

/-- The `(7,3)` atom split of the graphic `K4` design: atom `0` duplicated with its
weight halved. Every leverage is still `3`, so this is the `(7,3)` object the recorded
residue claim also names.

SCOPE, and it bounds everything downstream: `replicatedDesign_atom_last` makes the
fresh copy EQUAL to atom `0`, so this design satisfies `Gtz.HasParallelPair` and is
NON-PRIMITIVE. It was therefore never a candidate primitive `(7,3)` obstruction —
`Gtz.dominating_of_parallel_pair` folds any such design back one size, and here the
`(6,3)` original already dominates. What the `(7,3)` statements below add is only that
the recorded claim is false at the size the campaign cares about, not a new obstruction
at that size. -/
noncomputable def graphicKFourSevenDesign : WeightedDesign 7 3 :=
  replicatedDesign graphicKFourDesign 0

theorem graphicKFourSevenDesign_atom_castSucc (edge : Fin 6) :
    graphicKFourSevenDesign.atom edge.castSucc = graphicKFourDesign.atom edge := by
  rw [graphicKFourSevenDesign, ← atom_replicationMerge, replicationMerge_castSucc]

theorem graphicKFourSevenDesign_allHeavy : AllHeavy graphicKFourSevenDesign :=
  replicatedDesign_allHeavy graphicKFourDesign 0 graphicKFourDesign_allHeavy

theorem graphicKFourSevenDesign_heavyExcess_castSucc (edge : Fin 6) :
    heavyExcess graphicKFourSevenDesign edge.castSucc = 2 := by
  rw [heavyExcess_eq_of_atom_eq graphicKFourSevenDesign graphicKFourDesign
    (graphicKFourSevenDesign_atom_castSucc edge), graphicKFourDesign_heavyExcess]

theorem graphicKFourSevenDesign_atomPairing_castSucc (edgeFirst edgeSecond : Fin 6) :
    atomPairing graphicKFourSevenDesign edgeFirst.castSucc edgeSecond.castSucc
      = atomPairing graphicKFourDesign edgeFirst edgeSecond :=
  atomPairing_eq_of_atom_eq graphicKFourSevenDesign graphicKFourDesign
    (graphicKFourSevenDesign_atom_castSucc edgeFirst)
    (graphicKFourSevenDesign_atom_castSucc edgeSecond)

/-- Every one of the seven leverages is exactly `3`: the fresh copy carries atom `0`'s
vector. -/
theorem graphicKFourSevenDesign_leverage (edge : Fin 7) :
    leverageOf (graphicKFourSevenDesign.atom edge) = 3 := by
  refine Fin.lastCases ?_ ?_ edge
  · rw [graphicKFourSevenDesign, replicatedDesign_atom_last, graphicKFourDesign_leverage]
  · intro index
    rw [graphicKFourSevenDesign_atom_castSucc, graphicKFourDesign_leverage]

theorem graphicKFourSevenDesign_pairMinor_zeroTwo :
    pairMinor graphicKFourSevenDesign (0 : Fin 6).castSucc (2 : Fin 6).castSucc = 7 / 4 := by
  rw [pairMinor, graphicKFourSevenDesign_heavyExcess_castSucc,
    graphicKFourSevenDesign_heavyExcess_castSucc,
    graphicKFourSevenDesign_atomPairing_castSucc, graphicKFourDesign_atomPairing_zeroTwo]
  norm_num

theorem graphicKFourSevenDesign_pairMinor_zeroFour :
    pairMinor graphicKFourSevenDesign (0 : Fin 6).castSucc (4 : Fin 6).castSucc = 7 / 4 := by
  rw [pairMinor, graphicKFourSevenDesign_heavyExcess_castSucc,
    graphicKFourSevenDesign_heavyExcess_castSucc,
    graphicKFourSevenDesign_atomPairing_castSucc, graphicKFourDesign_atomPairing_zeroFour]
  norm_num

/-- **THE REFUTATION AT THE FRONTIER SIZE.** At the `(7,3)` atom split of the graphic
`K4` design — all-heavy, every leverage exactly `3` — the shipped product-floor cell
fires at the grid value `3/8` on the lifted star triple. So the recorded claim that no
shipped cell fires at any triple of this object is false at `(7,3)` as well as at
`(6,3)`, and `DiscriminantCovering 7` is not obstructed here. -/
theorem isInCell_productFloorCell_threeEighths_graphicKFourSeven :
    IsInCell (productFloorCell (3 / 8) ((0 : Fin 6).castSucc) ((2 : Fin 6).castSucc)
        ((4 : Fin 6).castSucc) (by decide) (by decide) (by decide))
      graphicKFourSevenDesign := by
  refine (isInCell_productFloorCell_iff graphicKFourSevenDesign (3 / 8)
    (by decide) (by decide) (by decide)).mpr ⟨?_, ?_, ?_, ?_⟩
  · rw [graphicKFourSevenDesign_pairMinor_zeroTwo]; norm_num
  · rw [graphicKFourSevenDesign_pairMinor_zeroFour]; norm_num
  · rw [graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourDesign_atomPairing_zeroTwo, graphicKFourDesign_atomPairing_zeroFour,
      graphicKFourDesign_atomPairing_twoFour]
    norm_num
  · rw [graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourDesign_atomPairing_zeroTwo, graphicKFourDesign_atomPairing_zeroFour,
      graphicKFourDesign_atomPairing_twoFour]
    norm_num

/-- The lifted star triple of the `(7,3)` split dominates, through the shipped cell. -/
theorem graphicKFourSevenDesign_dominates_liftedStarTriple :
    Dominates graphicKFourSevenDesign
      {(0 : Fin 6).castSucc, (2 : Fin 6).castSucc, (4 : Fin 6).castSucc} := by
  refine dominates_of_productFloor graphicKFourSevenDesign (by decide) (by decide)
    (by decide) (by rw [graphicKFourSevenDesign_leverage]; norm_num)
    (productFloor := 3 / 8) ?_ ?_ ?_ ?_
  · rw [graphicKFourSevenDesign_pairMinor_zeroTwo]; norm_num
  · rw [graphicKFourSevenDesign_pairMinor_zeroFour]; norm_num
  · rw [graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourDesign_atomPairing_zeroTwo, graphicKFourDesign_atomPairing_zeroFour,
      graphicKFourDesign_atomPairing_twoFour]
    norm_num
  · rw [graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_heavyExcess_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourSevenDesign_atomPairing_castSucc,
      graphicKFourDesign_atomPairing_zeroTwo, graphicKFourDesign_atomPairing_zeroFour,
      graphicKFourDesign_atomPairing_twoFour]
    norm_num

/-! ### Calibration of the new cells at the regular tetrahedron -/

theorem tetraDesign_pairMinor_zeroOne : pairMinor tetraDesign 0 1 = 3 := by
  rw [pairMinor, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
    tetraDesign_atomPairing_zeroOne]
  norm_num

theorem tetraDesign_pairMinor_zeroTwo : pairMinor tetraDesign 0 2 = 3 := by
  rw [pairMinor, tetraDesign_heavyExcess, tetraDesign_heavyExcess,
    tetraDesign_atomPairing_zeroTwo]
  norm_num

theorem tetraDesign_conditionalPairing : conditionalPairing tetraDesign 0 1 2 = -3 := by
  rw [conditionalPairing, tetraDesign_heavyExcess, tetraDesign_atomPairing_zeroOne,
    tetraDesign_atomPairing_zeroTwo, tetraDesign_atomPairing_oneTwo]
  norm_num

/-- **THE UNIT MEMBER IS EXACTLY TIGHT AT THE REGULAR TETRAHEDRON**, and so is the
parameter constraint. There `|conditionalPairing| = 3` equals BOTH pivot minors, so the
only admissible parameters are `paramFirst = paramSecond = 1` and their product is
exactly `1` — the corner of `paramFirst · paramSecond ≤ 1`. Both hypotheses of
`dominates_of_unitConditionalPairingBox` hold with equality, matching
`tetraDesign_discriminantTie = 0`: the cell has no slack at the campaign's sharpest
object, which is why the family had to be stated non-strictly. -/
theorem unitConditionalPairingBox_tight_at_tetraDesign :
    |conditionalPairing tetraDesign 0 1 2| = pairMinor tetraDesign 0 1
      ∧ |conditionalPairing tetraDesign 0 1 2| = pairMinor tetraDesign 0 2 := by
  rw [tetraDesign_conditionalPairing, tetraDesign_pairMinor_zeroOne,
    tetraDesign_pairMinor_zeroTwo]
  norm_num

/-- **THE PAIRING-FLOOR CELL IS BLIND AT THE REGULAR TETRAHEDRON.** Its floor must be
nonnegative and must sit below every pairing, and the tetrahedron's pairings are all
`−1`. So Cell B is genuinely weaker than Cell A rather than an alternative to it: it
reaches the acute over-unit stratum where the sign-blind body fails (`K4`), and it
misses the obtuse tie boundary entirely. Recorded so no reader mistakes the two cells
for a covering pair. -/
theorem pairingFloorCell_blind_at_tetraDesign : atomPairing tetraDesign 0 1 < 0 := by
  rw [tetraDesign_atomPairing_zeroOne]; norm_num

/-! ### The honesty ledger: what the pivot-minor hypotheses are buying -/

/-- **THE TIE LEG ALONE DOES NOT IMPLY THE TRACE LEG.** Six scalars with all three
heavy excesses strictly positive at which the tie leg is strictly positive and the
trace leg is strictly negative: excesses `(2,1,1)` and all three pairings `2`. So the
two pivot-minor hypotheses of both new cells are load-bearing — dropping them and
keeping only a bound that certifies the tie leg would certify a NON-dominating triple —
and the sign pattern behind the measured remark of
`Gtz.Quantitative.DiscriminantSystem` — whose "genuinely active" quantity is
`discriminantMinorSum`, the SECOND elementary symmetric function, not the trace leg —
is exhibited exactly here: at these scalars `discriminantMinorSum = −4 + (−3) = −7 < 0`
with the tie leg `+2 ≥ 0`. That remark is a statistic over sampled DESIGNS and this is
a scalar witness, so it sharpens the pattern without replacing the statistic.

SCOPE, and it is the whole scope. This is a statement about the six SCALARS a triple
presents, checked by `norm_num`, in exactly the shape `discriminantTie` and
`discriminantTrace` are defined. The Gram is realisable: the vectors `(1,1,1)`,
`(1,1,0)`, `(1,1,0)` in `R³` have self products `3, 2, 2` and pairwise products
`2, 2, 2`, hence these excesses and pairings. Whether a weighted `(7,3)` Parseval
design presents them at a triple is NOT established here — and note the realising
triple has two EQUAL vectors, so it is non-primitive and
`Gtz.dominating_of_parallel_pair` applies to any design containing it. -/
theorem tieLeg_alone_does_not_imply_traceLeg :
    ∃ excessPivot excessFirst excessSecond pairingPivotFirst pairingPivotSecond
        pairingPair : ℝ,
      0 < excessPivot ∧ 0 < excessFirst ∧ 0 < excessSecond
        ∧ 0 < excessPivot * (excessFirst * excessSecond - pairingPair ^ 2)
            - (excessSecond * pairingPivotFirst ^ 2
              - 2 * pairingPair * pairingPivotFirst * pairingPivotSecond
              + excessFirst * pairingPivotSecond ^ 2)
        ∧ (excessPivot * excessFirst - pairingPivotFirst ^ 2)
            + (excessPivot * excessSecond - pairingPivotSecond ^ 2) < 0
        ∧ excessFirst * excessSecond - pairingPair ^ 2 < 0 :=
  ⟨2, 1, 1, 2, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

end Gtz
