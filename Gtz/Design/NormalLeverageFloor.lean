/-
# The normal leverage floor and the line cap

`Gtz.sum_chartLeverage_eq_three` prices the WHOLE leverage budget at the rank.
Nothing priced a PART of it.  This module does, and the pricing is one
Cauchy-Schwarz.

Read the full-selection gap at a probe.  The gap is the slack Laplacian, so its
energy is the slack-weighted sum of squared readings.  Every label the probe
kills contributes nothing, so the whole energy sits on the labels that survive.
Cauchy-Schwarz through the resolvent prices each surviving square by that
label's own inverse form times the same energy.  The energy divides out and
leaves the surviving leverages above one.

Subtract from the rank.  The killed labels carry at most two.  A three-point
line has a common normal, so the leverages of a line total at most two.

That is the missing half of the three-lines counting argument.  A line cannot
fill the complement of the low-pivot set.  Filling it costs three units of
leverage-plus-weight, and a line has less than three: at most two of leverage,
and strictly less than one of weight because the labels off the line carry
positive weight.

This route needs no Schur complement, no block decomposition, no square root
and no eigenvalue.  It replaces the trace inequality `trace (U⁻¹ K) ≤ rank K`,
which was the previously planned brick.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.MarginTransfer
import Gtz.Design.DowndateInterlacing
import Gtz.Design.KFourDescentLadder
import Gtz.Design.ThreeLinesAtlas
import Gtz.Design.ThreeLinesAxisLaw
import Gtz.Design.ComplementPairCriterion

namespace Gtz

open Matrix

variable {size : ℕ}

/-! ### The energy of the full-selection gap -/

/-- The energy of the full-selection gap is the slack-weighted sum of squared
readings.  The full-selection gap IS the slack Laplacian. -/
theorem quadForm_directionChartGap_univ (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)
      = ∑ c, chartSlack mass weight c * (direction c ⬝ᵥ probe) ^ 2 := by
  rw [directionChartGap_univ_eq_slackLaplacian, slackLaplacian,
    Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]

/-- A positive definite full-selection gap reads positive at every nonzero
probe. -/
theorem quadForm_directionChartGap_univ_pos (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    {probe : Fin 3 → ℝ} (hne : probe ≠ 0) :
    0 < probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe) := by
  have hform := (Matrix.posDef_iff_dotProduct_mulVec.mp huniv).2 hne
  rwa [star_trivial] at hform

/-! ### The floor -/

/-- **THE NORMAL LEVERAGE FLOOR.**  If every label outside `F` reads zero at a
probe of positive energy, then the leverages of `F` alone total at least one.

The whole energy of the gap sits on `F`, and Cauchy-Schwarz through the
resolvent prices each of its squared readings by that label's inverse form
times the same energy.  Dividing by the energy leaves the floor. -/
theorem one_le_sum_chartLeverage_of_flat_outside (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ c, 0 ≤ chartSlack mass weight c)
    (probe : Fin 3 → ℝ)
    (hQ : 0 < probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe))
    (F : Finset (Fin size))
    (hflat : ∀ c, c ∉ F → direction c ⬝ᵥ probe = 0) :
    1 ≤ ∑ c ∈ F, chartLeverage direction mass weight c := by
  classical
  have hsym : (directionChartGap direction mass weight Finset.univ)ᵀ
      = directionChartGap direction mass weight Finset.univ :=
    directionChartGap_transpose direction mass weight Finset.univ
  -- the whole energy sits on `F`
  have hEnergy : probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)
      = ∑ c ∈ F, chartSlack mass weight c * (direction c ⬝ᵥ probe) ^ 2 := by
    rw [quadForm_directionChartGap_univ]
    refine (Finset.sum_subset (Finset.subset_univ F) ?_).symm
    intro c _ hc
    rw [hflat c hc]
    ring
  -- Cauchy-Schwarz through the resolvent, scaled by the slack
  have hCS : ∀ c ∈ F, chartSlack mass weight c * (direction c ⬝ᵥ probe) ^ 2
      ≤ chartLeverage direction mass weight c
        * (probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)) := by
    intro c _
    have hcs := pivot_prices_overlap huniv hsym (direction c) probe
    have hscaled := mul_le_mul_of_nonneg_left hcs (hslack c)
    calc chartSlack mass weight c * (direction c ⬝ᵥ probe) ^ 2
        ≤ chartSlack mass weight c
            * ((direction c ⬝ᵥ ((directionChartGap direction mass weight Finset.univ)⁻¹
                *ᵥ direction c))
              * (probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe))) :=
          hscaled
      _ = chartLeverage direction mass weight c
            * (probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)) := by
          rw [chartLeverage, fullInverseForm]
          ring
  have hsum : (∑ c ∈ F, chartSlack mass weight c * (direction c ⬝ᵥ probe) ^ 2)
      ≤ (∑ c ∈ F, chartLeverage direction mass weight c)
        * (probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hCS
  rw [← hEnergy] at hsum
  exact le_of_mul_le_mul_right (by linarith) hQ

/-! ### The cap -/

/-- **THE FLAT CAP.**  A set of labels that all read zero at a probe of positive
energy carries at most two units of leverage.  The rank is three and the
complement carries at least one. -/
theorem sum_chartLeverage_le_two_of_flat (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ c, 0 ≤ chartSlack mass weight c)
    (probe : Fin 3 → ℝ)
    (hQ : 0 < probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe))
    (flat : Finset (Fin size))
    (hflat : ∀ c ∈ flat, direction c ⬝ᵥ probe = 0) :
    ∑ c ∈ flat, chartLeverage direction mass weight c ≤ 2 := by
  classical
  have hfloor := one_le_sum_chartLeverage_of_flat_outside direction mass weight huniv hslack
    probe hQ flatᶜ (by
      intro c hc
      refine hflat c ?_
      by_contra hcf
      exact hc (Finset.mem_compl.mpr hcf))
  have htotal := sum_chartLeverage_eq_three direction mass weight huniv
  have hsplit : ∑ c ∈ flat, chartLeverage direction mass weight c
      + ∑ c ∈ flatᶜ, chartLeverage direction mass weight c
      = ∑ c, chartLeverage direction mass weight c :=
    Finset.sum_add_sum_compl flat _
  linarith

/-! ### A flat set cannot be the high-pivot complement -/

/-- **THE FLAT SET CANNOT STALL EVERY LABEL.**  A three-label flat set with a
label of positive weight outside it carries some label of full pivot below one.

Filling the flat set with high pivots costs three units of leverage plus
weight.  The cap gives at most two units of leverage, and the labels off the
flat set carry strictly positive weight, so the flat set carries strictly less
than one unit of weight. -/
theorem exists_fullPivot_lt_one_of_flat (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ)
    (huniv : (directionChartGap direction mass weight Finset.univ).PosDef)
    (hslack : ∀ c, 0 ≤ chartSlack mass weight c)
    (hweightPos : ∀ c, 0 < weight c) (hweightSum : ∑ c, weight c = 1)
    (hweightLtOne : ∀ c, weight c < 1)
    (probe : Fin 3 → ℝ)
    (hQ : 0 < probe ⬝ᵥ (directionChartGap direction mass weight Finset.univ *ᵥ probe))
    (flat : Finset (Fin size))
    (hflat : ∀ c ∈ flat, direction c ⬝ᵥ probe = 0)
    (hcard : flat.card = 3) (hcompl : flatᶜ.Nonempty) :
    ∃ c ∈ flat, fullPivot direction mass weight c < 1 := by
  classical
  by_contra hno
  push Not at hno
  -- every flat label carries leverage at least its own co-weight
  have hlev : ∀ c ∈ flat, 1 - weight c ≤ chartLeverage direction mass weight c := by
    intro c hc
    have hpivot := hno c hc
    have hco : (0 : ℝ) ≤ 1 - weight c := by linarith [hweightLtOne c]
    have := chartLeverage_eq_one_sub_weight_mul_fullPivot direction mass weight
      (i := c) (ne_of_gt (hweightPos c))
    nlinarith [this, hpivot, hco]
  have hsumlev : ∑ c ∈ flat, (1 - weight c)
      ≤ ∑ c ∈ flat, chartLeverage direction mass weight c :=
    Finset.sum_le_sum hlev
  have hleft : ∑ c ∈ flat, (1 - weight c)
      = 3 - ∑ c ∈ flat, weight c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hcard]
    norm_num
  -- the flat set carries strictly less than one unit of weight
  have hsplitw : ∑ c ∈ flat, weight c + ∑ c ∈ flatᶜ, weight c = 1 := by
    rw [Finset.sum_add_sum_compl flat weight, hweightSum]
  have hcomplpos : 0 < ∑ c ∈ flatᶜ, weight c :=
    Finset.sum_pos (fun c _ => hweightPos c) hcompl
  have hcap := sum_chartLeverage_le_two_of_flat direction mass weight huniv hslack probe hQ
    flat hflat
  linarith

/-! ### The three lines of the `#4` chart -/

/-- The first line `{0,1,2}` reads zero at the vertical axis. -/
theorem threeLines_firstLine_flat (slide : ℝ) (c : Fin 6)
    (hc : c ∈ ({0, 1, 2} : Finset (Fin 6))) :
    threeLinesDirection slide c ⬝ᵥ verticalProbe = 0 := by
  fin_cases hc <;>
    simp [threeLinesDirection, verticalProbe, dotProduct, Fin.sum_univ_three]

/-- The second line `{0,3,4}` reads zero at the second axis. -/
theorem threeLines_secondLine_flat (slide : ℝ) (c : Fin 6)
    (hc : c ∈ ({0, 3, 4} : Finset (Fin 6))) :
    threeLinesDirection slide c ⬝ᵥ secondAxisProbe = 0 := by
  fin_cases hc <;>
    simp [threeLinesDirection, secondAxisProbe, dotProduct, Fin.sum_univ_three]

/-- The third line `{1,3,5}` reads zero at the first axis. -/
theorem threeLines_thirdLine_flat (slide : ℝ) (c : Fin 6)
    (hc : c ∈ ({1, 3, 5} : Finset (Fin 6))) :
    threeLinesDirection slide c ⬝ᵥ firstAxisProbe = 0 := by
  fin_cases hc <;>
    simp [threeLinesDirection, firstAxisProbe, dotProduct, Fin.sum_univ_three]

/-! ### No line of the `#4` chart stalls every one of its labels -/

/-- **THE LINE CAP AT THE `#4` CHART.**  The leverages of a three-point line
total at most two, at every chart point with a positive definite full gap. -/
theorem threeLines_line_leverage_le_two (slide : ℝ) (point : DirectionChartPoint 6)
    (huniv : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      Finset.univ).PosDef)
    (line : Finset (Fin 6)) (probe : Fin 3 → ℝ) (hprobe : probe ≠ 0)
    (hflat : ∀ c ∈ line, threeLinesDirection slide c ⬝ᵥ probe = 0) :
    ∑ c ∈ line, chartLeverage (threeLinesDirection slide) point.mass point.weight c ≤ 2 :=
  sum_chartLeverage_le_two_of_flat _ _ _ huniv
    (fun c => (chartSlack_pos_of_chartPoint point c).le) probe
    (quadForm_directionChartGap_univ_pos _ _ _ huniv hprobe) line hflat

/-- **NO LINE STALLS EVERY ONE OF ITS LABELS.**  At every chart point of the
`#4` family with a positive definite full gap, each of the three lines carries a
label of full pivot below one.

Filling a line with high pivots costs three units of leverage plus weight.  The
cap gives the line at most two units of leverage, and the three labels off the
line carry strictly positive weight, so the line carries strictly less than one
unit of weight. -/
theorem threeLines_exists_fullPivot_lt_one_of_line (slide : ℝ) (point : DirectionChartPoint 6)
    (huniv : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      Finset.univ).PosDef)
    (line : Finset (Fin 6)) (probe : Fin 3 → ℝ) (hprobe : probe ≠ 0)
    (hflat : ∀ c ∈ line, threeLinesDirection slide c ⬝ᵥ probe = 0)
    (hcard : line.card = 3) (hcompl : lineᶜ.Nonempty) :
    ∃ c ∈ line, fullPivot (threeLinesDirection slide) point.mass point.weight c < 1 :=
  exists_fullPivot_lt_one_of_flat _ _ _ huniv
    (fun c => (chartSlack_pos_of_chartPoint point c).le)
    point.weight_pos point.weight_sum_one (chartPoint_weight_lt_one point) probe
    (quadForm_directionChartGap_univ_pos _ _ _ huniv hprobe) line hflat hcard hcompl

/-- The first line `{0,1,2}` carries a label of full pivot below one. -/
theorem threeLines_firstLine_exists_fullPivot_lt_one (slide : ℝ) (point : DirectionChartPoint 6)
    (huniv : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      Finset.univ).PosDef) :
    ∃ c ∈ ({0, 1, 2} : Finset (Fin 6)),
      fullPivot (threeLinesDirection slide) point.mass point.weight c < 1 :=
  threeLines_exists_fullPivot_lt_one_of_line slide point huniv _ verticalProbe
    verticalProbe_ne_zero (threeLines_firstLine_flat slide) (by decide)
    ⟨3, by decide⟩

/-- The second line `{0,3,4}` carries a label of full pivot below one. -/
theorem threeLines_secondLine_exists_fullPivot_lt_one (slide : ℝ) (point : DirectionChartPoint 6)
    (huniv : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      Finset.univ).PosDef) :
    ∃ c ∈ ({0, 3, 4} : Finset (Fin 6)),
      fullPivot (threeLinesDirection slide) point.mass point.weight c < 1 :=
  threeLines_exists_fullPivot_lt_one_of_line slide point huniv _ secondAxisProbe
    secondAxisProbe_ne_zero (threeLines_secondLine_flat slide) (by decide)
    ⟨1, by decide⟩

/-- The third line `{1,3,5}` carries a label of full pivot below one. -/
theorem threeLines_thirdLine_exists_fullPivot_lt_one (slide : ℝ) (point : DirectionChartPoint 6)
    (huniv : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      Finset.univ).PosDef) :
    ∃ c ∈ ({1, 3, 5} : Finset (Fin 6)),
      fullPivot (threeLinesDirection slide) point.mass point.weight c < 1 :=
  threeLines_exists_fullPivot_lt_one_of_line slide point huniv _ firstAxisProbe
    firstAxisProbe_ne_zero (threeLines_thirdLine_flat slide) (by decide)
    ⟨0, by decide⟩

/-! ### The line theorem -/

/-- The labels of full pivot below one.  A positive definite selection omits
only labels of this set. -/
noncomputable def lowPivotSet (slide : ℝ) (point : DirectionChartPoint 6) : Finset (Fin 6) :=
  Finset.univ.filter fun c =>
    fullPivot (threeLinesDirection slide) point.mass point.weight c < 1

theorem mem_lowPivotSet_iff (slide : ℝ) (point : DirectionChartPoint 6) (c : Fin 6) :
    c ∈ lowPivotSet slide point ↔
      fullPivot (threeLinesDirection slide) point.mass point.weight c < 1 := by
  simp [lowPivotSet]

/-- The three triples whose complements are the three lines.  An omitted triple
equal to one of these leaves a DEPENDENT selection, which can never be positive
definite. -/
def threeLinesDependentOmitted : Finset (Finset (Fin 6)) :=
  {{3, 4, 5}, {1, 2, 5}, {0, 2, 4}}

/-- **NO LINE FILLS THE COMPLEMENT OF THE LOW-PIVOT SET.**  Each of the three
lines meets the low-pivot set, so the low-pivot set is never exactly the
complement of a line. -/
theorem lowPivotSet_not_dependentOmitted (slide : ℝ) (point : DirectionChartPoint 6)
    (huniv : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      Finset.univ).PosDef) :
    lowPivotSet slide point ∉ threeLinesDependentOmitted := by
  classical
  intro hmem
  simp only [threeLinesDependentOmitted, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · obtain ⟨c, hc, hlt⟩ := threeLines_firstLine_exists_fullPivot_lt_one slide point huniv
    have : c ∈ lowPivotSet slide point := (mem_lowPivotSet_iff slide point c).mpr hlt
    rw [h] at this
    fin_cases hc <;> simp_all
  · obtain ⟨c, hc, hlt⟩ := threeLines_secondLine_exists_fullPivot_lt_one slide point huniv
    have : c ∈ lowPivotSet slide point := (mem_lowPivotSet_iff slide point c).mpr hlt
    rw [h] at this
    fin_cases hc <;> simp_all
  · obtain ⟨c, hc, hlt⟩ := threeLines_thirdLine_exists_fullPivot_lt_one slide point huniv
    have : c ∈ lowPivotSet slide point := (mem_lowPivotSet_iff slide point c).mpr hlt
    rw [h] at this
    fin_cases hc <;> simp_all

/-- **THE LINE THEOREM.**  At every chart point of the `#4` family with a
positive definite full gap, some triple of labels of full pivot below one leaves
an INDEPENDENT selection.

The pivot exclusion says a positive definite selection omits only labels of full
pivot below one, so this is the exact non-vacuity of the necessary condition.
Below four low-pivot labels the low-pivot set is the only candidate, and the
line cap keeps it off the three dependent triples.  At four or more the count of
candidate triples exceeds the count of dependent ones. -/
theorem threeLines_exists_admissible_omitted_triple (slide : ℝ)
    (point : DirectionChartPoint 6)
    (huniv : (directionChartGap (threeLinesDirection slide) point.mass point.weight
      Finset.univ).PosDef) :
    ∃ omitted : Finset (Fin 6), omitted ⊆ lowPivotSet slide point ∧ omitted.card = 3
      ∧ omitted ∉ threeLinesDependentOmitted := by
  classical
  have hthree : 3 ≤ (lowPivotSet slide point).card := by
    have := three_le_card_fullPivot_lt_one (threeLinesDirection slide) point huniv
    simpa [lowPivotSet] using this
  rcases eq_or_lt_of_le hthree with heq | hlt
  · exact ⟨lowPivotSet slide point, Finset.Subset.refl _, heq.symm,
      lowPivotSet_not_dependentOmitted slide point huniv⟩
  · -- four or more candidates: more triples than dependent ones
    have hfour : 4 ≤ (lowPivotSet slide point).card := hlt
    have hcount : 4 ≤ (Finset.powersetCard 3 (lowPivotSet slide point)).card := by
      rw [Finset.card_powersetCard]
      calc (4 : ℕ) = Nat.choose 4 3 := by norm_num
        _ ≤ Nat.choose (lowPivotSet slide point).card 3 := Nat.choose_le_choose 3 hfour
    have hbad : threeLinesDependentOmitted.card ≤ 3 := by decide
    by_contra hno
    push Not at hno
    have hsub : Finset.powersetCard 3 (lowPivotSet slide point)
        ⊆ threeLinesDependentOmitted := by
      intro omitted hom
      rw [Finset.mem_powersetCard] at hom
      by_contra hnot
      exact hnot (hno omitted hom.1 hom.2)
    have := Finset.card_le_card hsub
    omega

end Gtz
