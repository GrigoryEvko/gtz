/-
# The two pair conditions are exchanged by the sharp duality

`Gtz/Wave/ChartQuadraticCore.lean` puts both halves of the `(6,3)` hinge
dictionary in ONE `2 × 2` block of the chart gap `M`, read against two different
diagonal shifts:

    `(M_pp + t_p)(M_qq + t_q) - M_pq²`            vanishes at a PARALLEL PAIR
    `(1 - t_p - M_pp)(1 - t_q - M_qq) - M_pq²`    vanishes at FOUR COPLANAR atoms
                                                  on the complementary set.

`Gtz/Wave/ChartGapSharpDuality.lean` sends `M` to `M_E = -(N M⁻¹ N)`, the chart gap
of the sharp design.  This module proves that the duality EXCHANGES the two
readings:

  **`Gtz.chartParallelPair_iff_sharpCoPairDeterminant`.**  For distinct labels
  `p, q` of any design with two or more atoms,

      `(M_pp + t_p)(M_qq + t_q) = M_pq²`
        ⟺  `(1 - t_p - (M_E)_pp)(1 - t_q - (M_E)_qq) = (M_E)_pq²` .

The left side is the first shift on `M`.  The right side is the SECOND shift on
`M_E`.  So the parallel-pair condition of a design and the coplanar condition of
its sharp dual are the same equation, seen through the duality.

## Why it is true, and where the weights go

`M_E = 1 - diag t - Π` with `Π = Gtz.totalGapHat` the hat of the co-weighted frame,
so the second shift undoes the `1 - diag t` exactly:

    `1 - t_c - (M_E)_cc = Π_cc`   and   `(M_E)_pq = -Π_pq`   for `p ≠ q`.

The right side is therefore `Π_pp Π_qq - Π_pq²`, and reading `Π` off its frame
(`Gtz.totalGapHat_apply`) turns that into

    `(1 - t_p)(1 - t_q) · (ρ_p ρ_q - ⟨g_p, G⁻¹ g_q⟩²)` ,

the co-atom readings' own Gram defect.  The left side is
`t_p t_q · Gtz.pairGramMinor`, the Euclidean Gram defect.  The landed metric
transfer `Gtz.totalGapDefect_eq_zero_iff_leverageDefect_eq_zero` says those two
defects vanish together, because Cauchy–Schwarz equality is a statement about the
two VECTORS and not about the metric.

Both weight factors are strictly positive, so neither can make a defect vanish
spuriously — the exchange is exact and not merely up to a scale.

## Scope

The exchange holds at EVERY size and rank: nothing in it is special to `(6,3)`.
What IS special to `(6,3)` is the READING of the right side as coplanarity of four
atoms, because only there is the complement of a pair a four-set;
`Gtz.pairCapSlack_eq_zero_iff_fourCoplanar'` supplies that reading and this module
cites it rather than restating it.

Nothing here says the HINGE transports.  It does not:
`Gtz.hinge_not_preserved_by_duality` refutes that at `(k+1, k)` against
`(k+1, 1)`, and the reason is visible above — the exchange sends "parallel pair"
to a condition on the DUAL, which at a general cell is not "parallel pair" again.
At `(6,3)`, the Gale self-dual cell, the fifteen pairs and the fifteen
complementary quadruples do match up, and that is a fact about that cell alone.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Wave.SharpFiveSetCriterion
import Gtz.Wave.SharpShareCoAtom
import Gtz.Wave.ComplementVolumeRowLaw
import Gtz.Wave.ChartQuadraticCore
import Gtz.Wave.ChartGapSharpDuality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## Part 1 — a hat matrix off the diagonal

`Gtz.hat_diag_eq` reads a hat matrix on its diagonal.  Two labels need the same
double-sum swap and no more. -/

/-- **A HAT ENTRY IS THE PAIRING OF TWO ROWS IN THE METRIC.**  The off-diagonal
companion of `Gtz.hat_diag_eq`. -/
theorem hat_entry_eq {rows cols : ℕ} (frame : Matrix (Fin rows) (Fin cols) ℝ)
    (metric : Matrix (Fin cols) (Fin cols) ℝ) (leftLabel rightLabel : Fin rows) :
    (frame * metric * frameᵀ) leftLabel rightLabel
      = (fun coord => frame leftLabel coord)
        ⬝ᵥ (metric *ᵥ (fun coord => frame rightLabel coord)) := by
  have hleft : (frame * metric * frameᵀ) leftLabel rightLabel
      = ∑ rowCoord, ∑ colCoord,
          frame leftLabel rowCoord * metric rowCoord colCoord * frame rightLabel colCoord := by
    rw [Matrix.mul_apply]
    have hterm : ∀ colCoord : Fin cols,
        (frame * metric) leftLabel colCoord * frameᵀ colCoord rightLabel
          = ∑ rowCoord, frame leftLabel rowCoord * metric rowCoord colCoord
              * frame rightLabel colCoord := by
      intro colCoord
      rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun colCoord _ => hterm colCoord, Finset.sum_comm]
  have hright : (fun coord => frame leftLabel coord)
        ⬝ᵥ (metric *ᵥ (fun coord => frame rightLabel coord))
      = ∑ rowCoord, ∑ colCoord,
          frame leftLabel rowCoord * metric rowCoord colCoord * frame rightLabel colCoord := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun rowCoord _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun colCoord _ => by ring
  rw [hleft, hright]

/-- Scaling the two rows scales their pairing by the product of the two scales. -/
theorem reading_smul_pair {cols : ℕ} (metric : Matrix (Fin cols) (Fin cols) ℝ)
    (leftVec rightVec : Fin cols → ℝ) (leftScale rightScale : ℝ) :
    (fun coord => leftScale * leftVec coord)
        ⬝ᵥ (metric *ᵥ (fun coord => rightScale * rightVec coord))
      = leftScale * rightScale * (leftVec ⬝ᵥ (metric *ᵥ rightVec)) := by
  have hleft : (fun coord => leftScale * leftVec coord) = leftScale • leftVec := by
    funext coord; rw [Pi.smul_apply, smul_eq_mul]
  have hright : (fun coord => rightScale * rightVec coord) = rightScale • rightVec := by
    funext coord; rw [Pi.smul_apply, smul_eq_mul]
  rw [hleft, hright, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul]
  ring

/-- **THE HAT OF THE CO-WEIGHTED FRAME, ENTRYWISE.**  The two co-weight roots come
out and what is left is the pairing of the two atoms in the metric of the total
gap. -/
theorem totalGapHat_apply (D : WeightedDesign m k) (leftLabel rightLabel : Fin m) :
    totalGapHat D leftLabel rightLabel
      = coRoot D leftLabel * coRoot D rightLabel
        * (D.atom leftLabel ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom rightLabel)) := by
  have hleftRow : (fun coord => totalGapFrame D leftLabel coord)
      = fun coord => coRoot D leftLabel * D.atom leftLabel coord := by
    funext coord; rw [totalGapFrame, Matrix.of_apply]
  have hrightRow : (fun coord => totalGapFrame D rightLabel coord)
      = fun coord => coRoot D rightLabel * D.atom rightLabel coord := by
    funext coord; rw [totalGapFrame, Matrix.of_apply]
  rw [totalGapHat, hat_entry_eq, hleftRow, hrightRow, reading_smul_pair]

/-! ## Part 2 — the sharp gap against the second shift

The `1 - diag t` in `Gtz.sharpChartGap` is exactly what the second shift removes,
so the co-pair determinant of the sharp gap is a determinant of the hat. -/

/-- Off the diagonal the sharp chart gap is the NEGATED hat. -/
theorem sharpChartGap_apply_of_ne (D : WeightedDesign m k) {leftLabel rightLabel : Fin m}
    (hne : leftLabel ≠ rightLabel) :
    sharpChartGap D leftLabel rightLabel = -(totalGapHat D leftLabel rightLabel) := by
  rw [sharpChartGap, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_ne hne,
    Matrix.diagonal_apply_ne _ hne, sub_zero, zero_sub]

/-- The second shift of the sharp chart gap returns the hat's diagonal. -/
theorem one_sub_weight_sub_sharpChartGap_diagonal (D : WeightedDesign m k)
    (atomIndex : Fin m) :
    1 - D.weight atomIndex - sharpChartGap D atomIndex atomIndex
      = totalGapHat D atomIndex atomIndex := by
  rw [sharpChartGap, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.diagonal_apply_eq]
  ring

/-- **THE CO-PAIR DETERMINANT OF THE SHARP GAP IS THE CO-ATOM GRAM DEFECT.**  Both
co-weights come out as a strictly positive factor, and what is left is the Gram
defect of the two atoms in the metric of the total gap. -/
theorem sharpChartPairDeterminant_eq (D : WeightedDesign m k) (hm : 2 ≤ m)
    {leftLabel rightLabel : Fin m} (hne : leftLabel ≠ rightLabel) :
    (1 - D.weight leftLabel - sharpChartGap D leftLabel leftLabel)
        * (1 - D.weight rightLabel - sharpChartGap D rightLabel rightLabel)
        - sharpChartGap D leftLabel rightLabel ^ 2
      = (1 - D.weight leftLabel) * (1 - D.weight rightLabel)
        * (totalGapReading D leftLabel * totalGapReading D rightLabel
          - (D.atom leftLabel ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom rightLabel)) ^ 2) := by
  have hleft := one_sub_weight_sub_sharpChartGap_diagonal D leftLabel
  have hright := one_sub_weight_sub_sharpChartGap_diagonal D rightLabel
  have hoff := sharpChartGap_apply_of_ne D hne
  have hdiagLeft := totalGapHat_diag D hm leftLabel
  have hdiagRight := totalGapHat_diag D hm rightLabel
  have hentry := totalGapHat_apply D leftLabel rightLabel
  have hrootLeft := coRoot_sq D hm leftLabel
  have hrootRight := coRoot_sq D hm rightLabel
  rw [hleft, hright, hoff, hdiagLeft, hdiagRight, hentry]
  have hsquare : (coRoot D leftLabel * coRoot D rightLabel
        * (D.atom leftLabel ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom rightLabel))) ^ 2
      = (1 - D.weight leftLabel) * (1 - D.weight rightLabel)
        * (D.atom leftLabel ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom rightLabel)) ^ 2 := by
    rw [mul_pow, mul_pow, hrootLeft, hrootRight]
  rw [neg_pow, neg_one_pow_two, one_mul, hsquare]
  ring

/-! ## Part 3 — the exchange -/

/-- **THE DUALITY EXCHANGES THE TWO PAIR CONDITIONS.**  The FIRST diagonal shift of
the chart gap vanishes at a pair exactly when the SECOND diagonal shift of the
SHARP chart gap vanishes at the same pair.

At `(6,3)` the left side is a parallel pair of the design
(`Gtz.hasParallelPair_iff_chartCore`) and the right side is coplanarity of the four
complementary atoms of the sharp design
(`Gtz.pairCapSlack_eq_zero_iff_fourCoplanar'`).  The statement itself is valid at
every size and every rank. -/
theorem chartParallelPair_iff_sharpCoPairDeterminant (D : WeightedDesign m k) (hm : 2 ≤ m)
    {leftLabel rightLabel : Fin m} (hne : leftLabel ≠ rightLabel) :
    ((chartGapOfDesign D leftLabel leftLabel + D.weight leftLabel)
          * (chartGapOfDesign D rightLabel rightLabel + D.weight rightLabel)
        = chartGapOfDesign D leftLabel rightLabel ^ 2)
      ↔ ((1 - D.weight leftLabel - sharpChartGap D leftLabel leftLabel)
          * (1 - D.weight rightLabel - sharpChartGap D rightLabel rightLabel)
        = sharpChartGap D leftLabel rightLabel ^ 2) := by
  have hprimal := chartPairDeterminant_eq_weight_mul_pairGramMinor D hne
  have hdual := sharpChartPairDeterminant_eq D hm hne
  have hweightPos : (0 : ℝ) < D.weight leftLabel * D.weight rightLabel :=
    mul_pos (D.weight_pos leftLabel) (D.weight_pos rightLabel)
  have hcoPos : (0 : ℝ) < (1 - D.weight leftLabel) * (1 - D.weight rightLabel) :=
    mul_pos (by linarith [weight_lt_one D hm leftLabel])
      (by linarith [weight_lt_one D hm rightLabel])
  have htransfer :=
    totalGapDefect_eq_zero_iff_leverageDefect_eq_zero D hm leftLabel rightLabel
  constructor
  · intro hzero
    rw [hzero, sub_self] at hprimal
    have hminor : pairGramMinor D leftLabel rightLabel = 0 := by
      rcases mul_eq_zero.mp hprimal.symm with hbad | hgood
      · exact absurd hbad (ne_of_gt hweightPos)
      · exact hgood
    have hdefect : totalGapReading D leftLabel * totalGapReading D rightLabel
        - (D.atom leftLabel ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom rightLabel)) ^ 2 = 0 := by
      refine htransfer.mpr ?_
      rw [pairGramMinor] at hminor
      exact hminor
    rw [hdefect, mul_zero] at hdual
    linarith [hdual]
  · intro hzero
    rw [hzero, sub_self] at hdual
    have hdefect : totalGapReading D leftLabel * totalGapReading D rightLabel
        - (D.atom leftLabel ⬝ᵥ ((totalGap D)⁻¹ *ᵥ D.atom rightLabel)) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hdual.symm with hbad | hgood
      · exact absurd hbad (ne_of_gt hcoPos)
      · exact hgood
    have hminor : pairGramMinor D leftLabel rightLabel = 0 := by
      rw [pairGramMinor]
      exact htransfer.mp hdefect
    rw [hminor, mul_zero] at hprimal
    linarith [hprimal]

/-- **A PARALLEL PAIR OF THE DESIGN IS A CO-PAIR DEGENERACY OF THE SHARP GAP.**  The
same exchange with the left side read as `Gtz.HasParallelPair` rather than as a
determinant. -/
theorem hasParallelPair_iff_exists_sharpCoPairDeterminant (D : WeightedDesign m k)
    (hm : 2 ≤ m) :
    HasParallelPair D
      ↔ ∃ leftLabel rightLabel : Fin m, leftLabel ≠ rightLabel
          ∧ (1 - D.weight leftLabel - sharpChartGap D leftLabel leftLabel)
              * (1 - D.weight rightLabel - sharpChartGap D rightLabel rightLabel)
            = sharpChartGap D leftLabel rightLabel ^ 2 := by
  rw [hasParallelPair_iff_chartCore D]
  constructor
  · rintro ⟨leftLabel, rightLabel, hne, hzero⟩
    refine ⟨leftLabel, rightLabel, hne, ?_⟩
    refine (chartParallelPair_iff_sharpCoPairDeterminant D hm hne).mp ?_
    simpa only [chartCoreOfDesign_gap, chartCoreOfDesign_weight] using hzero
  · rintro ⟨leftLabel, rightLabel, hne, hzero⟩
    refine ⟨leftLabel, rightLabel, hne, ?_⟩
    have hstep := (chartParallelPair_iff_sharpCoPairDeterminant D hm hne).mpr hzero
    simpa only [chartCoreOfDesign_gap, chartCoreOfDesign_weight] using hstep

/-- **THE `(6,3)` READING.**  At six points and rank three the exchange says: the
pair `{p, q}` is parallel in the design exactly when the second shift of the sharp
chart gap is singular at that pair — and the landed complementary volume row law
reads THAT as coplanarity of the four atoms of the complementary set in the sharp
design.

The four labels are carried as hypotheses because the reading of the right side,
unlike the exchange itself, is a fact about this cell: only at `(6,3)` is the
complement of a pair a four-set. -/
theorem sixThree_sharp_pair_exchange (D : WeightedDesign 6 3)
    {leftLabel rightLabel : Fin 6} (hne : leftLabel ≠ rightLabel) :
    (pairGramMinor D leftLabel rightLabel = 0)
      ↔ ((1 - D.weight leftLabel - sharpChartGap D leftLabel leftLabel)
          * (1 - D.weight rightLabel - sharpChartGap D rightLabel rightLabel)
        = sharpChartGap D leftLabel rightLabel ^ 2) := by
  have hm : (2 : ℕ) ≤ 6 := by norm_num
  have hbridge := chartPairDeterminant_eq_weight_mul_pairGramMinor D hne
  have hweightPos : (0 : ℝ) < D.weight leftLabel * D.weight rightLabel :=
    mul_pos (D.weight_pos leftLabel) (D.weight_pos rightLabel)
  rw [← chartParallelPair_iff_sharpCoPairDeterminant D hm hne]
  constructor
  · intro hminor
    rw [hminor, mul_zero] at hbridge
    linarith [hbridge]
  · intro hzero
    rw [hzero, sub_self] at hbridge
    rcases mul_eq_zero.mp hbridge.symm with hbad | hgood
    · exact absurd hbad (ne_of_gt hweightPos)
    · exact hgood

end Gtz
