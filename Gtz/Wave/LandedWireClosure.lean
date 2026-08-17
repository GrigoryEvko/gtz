import Gtz.Wave.FlatPairWeakSeed
import Gtz.Wave.TriangleStallClosureDeflation
import Gtz.Wave.OffsetUpperBound

/-!
# Four landed pairs, joined

Each section below closes one pair of landed results that speak the same
mathematics in two vocabularies and had no bridge between them.

1. **The polarized gap reading.**  Every reading of the gap form in the corpus is
   DIAGONAL, `p ⬝ᵥ (G *ᵥ p)`.  So `Gtz.gapDiscriminant_eq_wedgeBalance`, which is
   a two by two minor law, is written longhand and is never recognised as one.
   The polarized reading supplies the cross term, and the master identity becomes
   a matrix statement: the gap minor at two vectors IS `Gtz.wedgeBalanceValue`.
   `Gtz.WedgeBalanceAt` then becomes a MINOR SIGN, at every rank.
2. **The weak projection bridge.**  `Gtz.posDef_blockGapAt_iff_subsetSum` carries
   the STRICT half only.  `Gtz.Dominates` is the weak half and it is one `rfl`
   away, through `Gtz.blockGapAt_eq_projectionBlockGap`.
3. **The discarded margin.**  `Gtz.posDef_on_orthogonal_of_deflatedGapBound`
   derives a quantitative bound and then throws it away, keeping only the sign.
   The bound survives here, in a division-free product form that needs no
   positivity at all.
4. **The tie witness at `K4`.**  `Gtz.not_isTie_of_detWitness` refutes a tie from
   one deflated bound and one determinant sign, at every rank and every size, and
   it has no consumer.  `Gtz.kFour_exists_deflatedSubset` produces exactly that
   bound at every `K4` chart point, unconditionally.
-/

namespace Gtz

open Matrix

/-! ## 1. The polarized gap reading, and the master identity as a minor law -/

/-- **THE POLARIZED GAP READING.**  The corpus carries only the diagonal reading
`Gtz.dotProduct_subsetSum_sub_one_mulVec_eq_sumSq`.  The gap is bilinear, so the
two-vector reading holds as well, and a two by two minor needs it. -/
theorem dotProduct_subsetSum_sub_one_mulVec_polarized {size rank : ℕ}
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (normalVec probeVec : Fin rank → ℝ) :
    normalVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec)
      = (∑ label ∈ selected,
          (design.atom label ⬝ᵥ normalVec) * (design.atom label ⬝ᵥ probeVec))
        - normalVec ⬝ᵥ probeVec := by
  rw [subsetSum, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, Matrix.sum_mulVec,
    dotProduct_sum]
  congr 1
  exact Finset.sum_congr rfl fun label _ =>
    dotProduct_atomMatrix_mulVec_cross (design.atom label) normalVec probeVec

/-- **THE MASTER IDENTITY IS A MINOR LAW.**  The left side of
`Gtz.gapDiscriminant_eq_wedgeBalance` is the two by two Gram minor of the gap
matrix at the two vectors, and the right side is `Gtz.wedgeBalanceValue`.  Neither
reading was in the tree.  No hypothesis, any subset, any rank. -/
theorem gapMinor_eq_wedgeBalanceValue {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) :
    (normalVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ normalVec))
        * (probeVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec))
      - (normalVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec)) ^ 2
      = wedgeBalanceValue design selected normalVec probeVec := by
  rw [dotProduct_subsetSum_sub_one_mulVec_eq_sumSq,
    dotProduct_subsetSum_sub_one_mulVec_eq_sumSq,
    dotProduct_subsetSum_sub_one_mulVec_polarized, wedgeBalanceValue]
  exact gapDiscriminant_eq_wedgeBalance design selected normalVec probeVec

/-- **THE WEDGE BALANCE IS A MINOR SIGN.**  `Gtz.WedgeBalanceAt` holds exactly
when the two by two gap minor at the two vectors is positive.  Every rank, every
subset, no hypothesis.  The wedge vocabulary and the matrix vocabulary are one
statement. -/
theorem wedgeBalanceAt_iff_pos_gapMinor {size rank : ℕ} (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (normalVec probeVec : Fin rank → ℝ) :
    WedgeBalanceAt design selected normalVec probeVec
      ↔ 0 < (normalVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ normalVec))
            * (probeVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec))
          - (normalVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec)) ^ 2 := by
  rw [gapMinor_eq_wedgeBalanceValue]
  exact wedgeBalanceAt_iff_pos_wedgeBalanceValue design selected normalVec probeVec

/-! ## 2. The weak half of the projection bridge

The tree carries the STRICT reading of a block of the projection form against a
subset sum.  The weak reading is the same `rfl` with `PosSemidef` in place of
`PosDef`, and `Gtz.Dominates` is exactly that. -/

/-- **DOMINATION IS THE PROJECTION BLOCK GAP, WEAKLY.**  The weak counterpart of
`Gtz.posDef_blockGapAt_iff_subsetSum`, in the `blockGapAt` vocabulary the
complement lane speaks. -/
theorem dominates_iff_posSemidef_blockGapAt {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : selected.card = 3) :
    Dominates design selected
      ↔ (blockGapAt (projectionOfDesign design) design.weight
          ((selected.orderEmbOfFin hcard : Fin 3 ↪o Fin size) : Fin 3 → Fin size)).PosSemidef := by
  rw [blockGapAt_eq_projectionBlockGap design selected hcard, projectionBlockGap]
  exact dominates_iff_posSemidef_projectionBlock_finset design selected hcard

/-! ## 3. The margin the deflated bound really carries

`Gtz.posDef_on_orthogonal_of_deflatedGapBound` reaches a quantitative inequality
and then spends it on a sign.  Stated as a product there is no division, no
positivity and no size hypothesis: only the orthogonality is used. -/

/-- **THE DEFLATED BOUND CARRIES A MARGIN, NOT ONLY A SIGN.**  On every direction
orthogonal to the dropped atom the gap form clears the dropped weight against the
probe energy, scaled by the surviving mass.  Division free. -/
theorem quadForm_margin_of_deflatedGapBound {m k : ℕ} (D : WeightedDesign (m + 1) k)
    (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
      - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef)
    (probeVec : Fin k → ℝ) (hOrthogonal : D.atom dropLabel ⬝ᵥ probeVec = 0) :
    D.weight dropLabel * (probeVec ⬝ᵥ probeVec)
      ≤ (1 - D.weight dropLabel)
        * (probeVec ⬝ᵥ ((subsetSum D selected - 1) *ᵥ probeVec)) := by
  have hInnerComplement : probeVec ⬝ᵥ
        (((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel)) *ᵥ probeVec)
      = probeVec ⬝ᵥ probeVec := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm probeVec (D.atom dropLabel), hOrthogonal, mul_zero, sub_zero]
  have hBoundForm := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 probeVec
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    hInnerComplement] at hBoundForm
  linarith [hBoundForm]

/-- The same margin, read through the named deflated bound. -/
theorem quadForm_margin_of_deflatedGapBoundAt {size rank : ℕ}
    (design : WeightedDesign size rank) (dropLabel : Fin size) (selected : Finset (Fin size))
    (hbound : DeflatedGapBoundAt design dropLabel selected)
    (probeVec : Fin rank → ℝ) (hOrthogonal : design.atom dropLabel ⬝ᵥ probeVec = 0) :
    design.weight dropLabel * (probeVec ⬝ᵥ probeVec)
      ≤ (1 - design.weight dropLabel)
        * (probeVec ⬝ᵥ ((subsetSum design selected - 1) *ᵥ probeVec)) := by
  have hInnerComplement : probeVec ⬝ᵥ
        (((1 : Matrix (Fin rank) (Fin rank) ℝ)
            - atomMatrix (design.atom dropLabel)) *ᵥ probeVec)
      = probeVec ⬝ᵥ probeVec := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm probeVec (design.atom dropLabel), hOrthogonal, mul_zero, sub_zero]
  have hBoundForm := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 probeVec
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    hInnerComplement] at hBoundForm
  linarith [hBoundForm]

/-! ## 4. The tie witness, fired at every `K4` chart point

`Gtz.not_isTie_of_detWitness` needs one deflated bound and one determinant sign,
at every rank and every size.  `Gtz.kFour_exists_deflatedSubset` supplies the
bound at every `K4` chart point and every label, with no hypothesis. -/

/-- **ONE DETERMINANT SIGN REFUTES THE TIE AT EVERY `K4` CHART POINT.**  The
deflation produces a design welded to the chart point and a card-three subset
avoiding the dropped label, on which a positive gap determinant refutes the tie
outright.  No stall, no wall, no heaviness and no leverage floor. -/
theorem kFour_exists_deflatedSubset_detWitness (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) :
    ∃ (design : WeightedDesign 6 3) (selected : Finset (Fin 6)),
      design.weight = point.weight ∧ selected.card = 3 ∧ dropLabel ∉ selected
        ∧ (0 < (subsetSum design selected - 1).det → ¬ IsTie design)
        ∧ ((directionChartGap kFourDirection point.mass point.weight selected).PosDef
          ↔ 0 < (subsetSum design selected - 1).det) := by
  obtain ⟨design, selected, hweight, hcard, hnotMem, hbound, hiff⟩ :=
    kFour_exists_deflatedSubset point dropLabel
  refine ⟨design, selected, hweight, hcard, hnotMem, ?_, hiff⟩
  intro hdet
  exact not_isTie_of_detWitness (by norm_num) design dropLabel selected hcard hbound hdet

/-- **THE CHART READING OF THE SAME WITNESS.**  Strict domination of the produced
subset IN THE CHART already refutes the tie of the welded design, so the whole
tie question at a `K4` chart point is one chart gap. -/
theorem kFour_exists_deflatedSubset_chartWitness (point : DirectionChartPoint 6)
    (dropLabel : Fin 6) :
    ∃ (design : WeightedDesign 6 3) (selected : Finset (Fin 6)),
      design.weight = point.weight ∧ selected.card = 3 ∧ dropLabel ∉ selected
        ∧ ((directionChartGap kFourDirection point.mass point.weight selected).PosDef
          → ¬ IsTie design) := by
  obtain ⟨design, selected, hweight, hcard, hnotMem, hwitness, hiff⟩ :=
    kFour_exists_deflatedSubset_detWitness point dropLabel
  exact ⟨design, selected, hweight, hcard, hnotMem,
    fun hposDef => hwitness (hiff.mp hposDef)⟩

end Gtz
