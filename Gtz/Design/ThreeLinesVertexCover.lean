import Gtz.Design.ChartReadingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The vertex cover cell of the three-lines chart

The covering criterion of `ChartReadingLaw` asks a selection to hold a maximal
kappa reading at EVERY probe.  That is a `forall`-probe condition, and until now
the tree carried no way to discharge it other than exhibiting the maximum.  This
module supplies one, and then reads the three-lines chart through it.

**The pair-domination lemma.**  Let a label `f` outside the selection satisfy a
pointwise quadratic bound `r_f <= alpha * r_a + beta * r_b` against two selected
labels, with `r` the squared probe reading.  If `2 * alpha * kappa_f <= kappa_a`
and `2 * beta * kappa_f <= kappa_b`, then the reading of `f` never exceeds the
larger of the two selected readings.  The factor two is the cost of splitting a
maximum into a mean, and it is what makes the criterion checkable by scalars.

**The three-lines instance.**  The chart directions are `v0 = e1`, `v1 = e2`,
`v3 = e3` with joins `v2 = v0 + v1`, `v4 = v0 + v3` and `v5 = v1 + slide * v3`.
Each join is a sum of exactly two vertex directions, so each join label admits a
pair domination against its two vertices with `alpha = beta = 2`, or with
`beta = 2 * slide ^ 2` for the sliding label.  Six scalar inequalities therefore
force the vertex triple `{0, 1, 3}` to cover, and the triple is then positive
definite with no minor computation and no tie analysis.

**The escape is exact and it is sharp.**  At the probe `(1, 1, 0)` the join `2`
reads four times its kappa while the vertices `0` and `1` read theirs once and
the vertex `3` reads zero.  So the vertex triple fails to cover as soon as
`4 * kappa_2` exceeds BOTH `kappa_0` and `kappa_1`.  The cell asks the same
quantity to fall below the MINIMUM of the two.  Between the minimum and the
maximum lies a band this cell does not decide, and the band is genuine.

**The axis probes force the triple.**  At the three coordinate axes the chart
reads the three complements of the lines, namely `{0,2,4}`, `{1,2,5}` and
`{3,4,5}`.  When each vertex strictly beats the joins its axis sees, the maximum
at that axis is unique and every covering selection must hold that vertex.  A
card-three covering selection is then exactly `{0, 1, 3}`, so the escape above
kills the reading-cover cell outright rather than merely one candidate.
-/

namespace Gtz

open Matrix Finset

/-! ## The pair-domination lemma -/

/-- **Weighted pair domination.**  A maximum dominates every convex combination
of its two arguments, so a reading bounded by a nonnegative combination of two
others never exceeds the larger of the two as soon as the two coefficients are
paid at complementary shares `share` and `1 - share` of the kappa ratios.

The share is the second free parameter of the criterion, and it is what makes
the family sharp.  Fixing `share = 1/2` recovers the mean split and its factor
two. -/
theorem reading_le_max_of_weightedPairDomination
    {kappaF kappaA kappaB alpha beta share readA readB readF : ℝ}
    (hkappaF : 0 ≤ kappaF) (hreadA : 0 ≤ readA) (hreadB : 0 ≤ readB)
    (hshareLow : 0 ≤ share) (hshareHigh : share ≤ 1)
    (hbound : readF ≤ alpha * readA + beta * readB)
    (hpayA : alpha * kappaF ≤ share * kappaA)
    (hpayB : beta * kappaF ≤ (1 - share) * kappaB) :
    kappaF * readF ≤ max (kappaA * readA) (kappaB * readB) := by
  have hsplit : kappaF * readF ≤ alpha * kappaF * readA + beta * kappaF * readB := by
    have := mul_le_mul_of_nonneg_left hbound hkappaF
    nlinarith [this]
  have hlegA : alpha * kappaF * readA ≤ share * kappaA * readA :=
    mul_le_mul_of_nonneg_right hpayA hreadA
  have hlegB : beta * kappaF * readB ≤ (1 - share) * kappaB * readB :=
    mul_le_mul_of_nonneg_right hpayB hreadB
  have hleftLe : kappaA * readA ≤ max (kappaA * readA) (kappaB * readB) := le_max_left _ _
  have hrightLe : kappaB * readB ≤ max (kappaA * readA) (kappaB * readB) := le_max_right _ _
  have hconvexA : share * kappaA * readA
      ≤ share * max (kappaA * readA) (kappaB * readB) := by
    have := mul_le_mul_of_nonneg_left hleftLe hshareLow
    nlinarith [this]
  have hconvexB : (1 - share) * kappaB * readB
      ≤ (1 - share) * max (kappaA * readA) (kappaB * readB) := by
    have hnonneg : (0 : ℝ) ≤ 1 - share := by linarith
    have := mul_le_mul_of_nonneg_left hrightLe hnonneg
    nlinarith [this]
  linarith

/-- **Pair domination at the mean split.**  Each coefficient paid twice over in
the kappa ratios.  The two is the price of bounding a maximum below by a mean,
and this is the `share = 1/2` member of the weighted family. -/
theorem reading_le_max_of_pairDomination {kappaF kappaA kappaB alpha beta readA readB readF : ℝ}
    (hkappaF : 0 ≤ kappaF) (hreadA : 0 ≤ readA) (hreadB : 0 ≤ readB)
    (hbound : readF ≤ alpha * readA + beta * readB)
    (hpayA : 2 * alpha * kappaF ≤ kappaA) (hpayB : 2 * beta * kappaF ≤ kappaB) :
    kappaF * readF ≤ max (kappaA * readA) (kappaB * readB) :=
  reading_le_max_of_weightedPairDomination (share := 1 / 2) hkappaF hreadA hreadB
    (by norm_num) (by norm_num) hbound (by linarith) (by linarith)

/-- A selected reading never exceeds the running maximum of the three vertex
readings. -/
theorem le_max_three_left {a b c : ℝ} : a ≤ max a (max b c) := le_max_left _ _

theorem le_max_three_mid {a b c : ℝ} : b ≤ max a (max b c) :=
  le_trans (le_max_left _ _) (le_max_right _ _)

theorem le_max_three_right {a b c : ℝ} : c ≤ max a (max b c) :=
  le_trans (le_max_right _ _) (le_max_right _ _)

/-- The maximum of three reals is one of them. -/
theorem max_three_eq {a b c : ℝ} :
    max a (max b c) = a ∨ max a (max b c) = b ∨ max a (max b c) = c := by
  rcases le_total b c with hbc | hbc
  · rcases le_total a c with hac | hac
    · exact Or.inr (Or.inr (by rw [max_eq_right hbc, max_eq_right hac]))
    · exact Or.inl (by rw [max_eq_right hbc, max_eq_left hac])
  · rcases le_total a b with hab | hab
    · exact Or.inr (Or.inl (by rw [max_eq_left hbc, max_eq_right hab]))
    · exact Or.inl (by rw [max_eq_left hbc, max_eq_left hab])

/-! ## The six chart readings -/

/-- The squared probe readings of the three-lines chart, label by label. -/
theorem threeLinesDirection_dotProduct (slide : ℝ) (probe : Fin 3 → ℝ) :
    threeLinesDirection slide 0 ⬝ᵥ probe = probe 0
      ∧ threeLinesDirection slide 1 ⬝ᵥ probe = probe 1
      ∧ threeLinesDirection slide 2 ⬝ᵥ probe = probe 0 + probe 1
      ∧ threeLinesDirection slide 3 ⬝ᵥ probe = probe 2
      ∧ threeLinesDirection slide 4 ⬝ᵥ probe = probe 0 + probe 2
      ∧ threeLinesDirection slide 5 ⬝ᵥ probe = probe 1 + slide * probe 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [threeLinesDirection_zero, threeLinesDirection_one, threeLinesDirection_two,
      threeLinesDirection_three, threeLinesDirection_four, threeLinesDirection_five,
      dotProduct, Fin.sum_univ_three]

/-- The join of two coordinates is dominated by twice the two squares. -/
theorem sq_add_le_two_mul (x y : ℝ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- The sliding join is dominated by twice the square and twice the scaled
square. -/
theorem sq_add_smul_le_two_mul (slide y z : ℝ) :
    (y + slide * z) ^ 2 ≤ 2 * y ^ 2 + 2 * slide ^ 2 * z ^ 2 := by
  nlinarith [sq_nonneg (y - slide * z)]

/-! ## The cell -/

/-- **The vertex cover cell.**  Six scalar inequalities in the kappa ratios and
the slide.  Each join label is paid for against the two vertices whose sum it
is, at the factor two of the pair-domination lemma squared. -/
def ThreeLinesVertexCoverCellFires (slide : ℝ) (point : DirectionChartPoint 6) : Prop :=
  4 * (point.mass 2 / point.weight 2) ≤ point.mass 0 / point.weight 0
    ∧ 4 * (point.mass 2 / point.weight 2) ≤ point.mass 1 / point.weight 1
    ∧ 4 * (point.mass 4 / point.weight 4) ≤ point.mass 0 / point.weight 0
    ∧ 4 * (point.mass 4 / point.weight 4) ≤ point.mass 3 / point.weight 3
    ∧ 4 * (point.mass 5 / point.weight 5) ≤ point.mass 1 / point.weight 1
    ∧ 4 * slide ^ 2 * (point.mass 5 / point.weight 5) ≤ point.mass 3 / point.weight 3

/-- **The cell forces the cover.**  Under the six inequalities the vertex triple
holds a maximal kappa reading at every probe. -/
theorem readingCover_vertexTriple_of_cellFires (slide : ℝ) (point : DirectionChartPoint 6)
    (hcell : ThreeLinesVertexCoverCellFires slide point) :
    ∀ probe : Fin 3 → ℝ, ∃ good ∈ ({0, 1, 3} : Finset (Fin 6)), ∀ label,
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
        ≤ point.mass good / point.weight good
          * (threeLinesDirection slide good ⬝ᵥ probe) ^ 2 := by
  obtain ⟨hjoin2A, hjoin2B, hjoin4A, hjoin4B, hjoin5A, hjoin5B⟩ := hcell
  intro probe
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := threeLinesDirection_dotProduct slide probe
  set kappa : Fin 6 → ℝ := fun label => point.mass label / point.weight label with hkappa
  have hkappaNonneg : ∀ label, 0 ≤ kappa label := fun label =>
    le_of_lt (div_pos (point.mass_pos label) (point.weight_pos label))
  set vertexA : ℝ := kappa 0 * probe 0 ^ 2 with hvertexA
  set vertexB : ℝ := kappa 1 * probe 1 ^ 2 with hvertexB
  set vertexC : ℝ := kappa 3 * probe 2 ^ 2 with hvertexC
  have hsqA : (0 : ℝ) ≤ probe 0 ^ 2 := sq_nonneg _
  have hsqB : (0 : ℝ) ≤ probe 1 ^ 2 := sq_nonneg _
  have hsqC : (0 : ℝ) ≤ probe 2 ^ 2 := sq_nonneg _
  have hbound2 : kappa 2 * (probe 0 + probe 1) ^ 2 ≤ max vertexA vertexB :=
    reading_le_max_of_pairDomination (hkappaNonneg 2) hsqA hsqB
      (sq_add_le_two_mul _ _) (by linarith) (by linarith)
  have hbound4 : kappa 4 * (probe 0 + probe 2) ^ 2 ≤ max vertexA vertexC :=
    reading_le_max_of_pairDomination (hkappaNonneg 4) hsqA hsqC
      (sq_add_le_two_mul _ _) (by linarith) (by linarith)
  have hbound5 : kappa 5 * (probe 1 + slide * probe 2) ^ 2 ≤ max vertexB vertexC :=
    reading_le_max_of_pairDomination (hkappaNonneg 5) hsqB hsqC
      (sq_add_smul_le_two_mul _ _ _) (by linarith) (by nlinarith)
  have hcase0 : kappa 0 * (threeLinesDirection slide 0 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by rw [hd0]; exact le_max_three_left
  have hcase1 : kappa 1 * (threeLinesDirection slide 1 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by rw [hd1]; exact le_max_three_mid
  have hcase2 : kappa 2 * (threeLinesDirection slide 2 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by
    rw [hd2]; exact le_trans hbound2 (max_le le_max_three_left le_max_three_mid)
  have hcase3 : kappa 3 * (threeLinesDirection slide 3 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by rw [hd3]; exact le_max_three_right
  have hcase4 : kappa 4 * (threeLinesDirection slide 4 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by
    rw [hd4]; exact le_trans hbound4 (max_le le_max_three_left le_max_three_right)
  have hcase5 : kappa 5 * (threeLinesDirection slide 5 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by
    rw [hd5]; exact le_trans hbound5 (max_le le_max_three_mid le_max_three_right)
  have hpeak : ∀ label, kappa label * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by
    intro label
    fin_cases label
    · exact hcase0
    · exact hcase1
    · exact hcase2
    · exact hcase3
    · exact hcase4
    · exact hcase5
  rcases max_three_eq (a := vertexA) (b := vertexB) (c := vertexC) with heq | heq | heq
  · refine ⟨0, by decide, fun label => ?_⟩
    rw [hd0]
    exact le_trans (hpeak label) (le_of_eq heq)
  · refine ⟨1, by decide, fun label => ?_⟩
    rw [hd1]
    exact le_trans (hpeak label) (le_of_eq heq)
  · refine ⟨3, by decide, fun label => ?_⟩
    rw [hd3]
    exact le_trans (hpeak label) (le_of_eq heq)

/-- **The cell fires.**  Six scalar inequalities give a strictly dominating
vertex triple at the chart point, with no minor and no tie analysis. -/
theorem posDef_threeLines_vertexTriple_of_cellFires (slide : ℝ)
    (point : DirectionChartPoint 6) (hcell : ThreeLinesVertexCoverCellFires slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_threeLines_of_readingCover slide point (by decide)
    (readingCover_vertexTriple_of_cellFires slide point hcell)

/-- **The strict triple from the cell.**  The chart point carries a card-three
strictly dominating selection. -/
theorem exists_posDef_threeLines_of_vertexCoverCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) (hcell : ThreeLinesVertexCoverCellFires slide point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight selected).PosDef :=
  ⟨{0, 1, 3}, by decide, posDef_threeLines_vertexTriple_of_cellFires slide point hcell⟩

/-! ## The escape, at the diagonal probe -/

/-- The diagonal probe of the first two coordinates. -/
def diagonalProbe : Fin 3 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 0

theorem diagonalProbe_ne_zero : diagonalProbe ≠ 0 := by
  intro hzero
  have := congrFun hzero 0
  norm_num [diagonalProbe] at this

/-- **The escape is exact.**  At the diagonal probe the join `2` reads four
times its kappa, the vertices `0` and `1` read theirs once, and the vertex `3`
reads zero.  So the vertex triple fails to cover as soon as four times
`kappa_2` beats both. -/
theorem not_readingCover_vertexTriple_of_join_heavy (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hbeatFirst : point.mass 0 / point.weight 0 < 4 * (point.mass 2 / point.weight 2))
    (hbeatSecond : point.mass 1 / point.weight 1 < 4 * (point.mass 2 / point.weight 2)) :
    ¬ (∃ good ∈ ({0, 1, 3} : Finset (Fin 6)), ∀ label,
        point.mass label / point.weight label
            * (threeLinesDirection slide label ⬝ᵥ diagonalProbe) ^ 2
          ≤ point.mass good / point.weight good
            * (threeLinesDirection slide good ⬝ᵥ diagonalProbe) ^ 2) := by
  obtain ⟨hd0, hd1, hd2, hd3, _, _⟩ := threeLinesDirection_dotProduct slide diagonalProbe
  have hp0 : diagonalProbe 0 = 1 := rfl
  have hp1 : diagonalProbe 1 = 1 := rfl
  have hp2 : diagonalProbe 2 = 0 := rfl
  have hjoinPos : 0 < point.mass 2 / point.weight 2 :=
    div_pos (point.mass_pos 2) (point.weight_pos 2)
  rintro ⟨good, hgoodMem, hgood⟩
  have hjoin := hgood 2
  rw [hd2, hp0, hp1] at hjoin
  simp only [Finset.mem_insert, Finset.mem_singleton] at hgoodMem
  rcases hgoodMem with rfl | rfl | rfl
  · rw [hd0, hp0] at hjoin; norm_num at hjoin; linarith
  · rw [hd1, hp1] at hjoin; norm_num at hjoin; linarith
  · rw [hd3, hp2] at hjoin; norm_num at hjoin; linarith

/-! ## The axis probes force the covering triple

At the three coordinate axes the chart reads the three complements of the lines.
When a vertex strictly beats the two joins its axis sees, that vertex is the
unique maximum there, so every covering selection holds it. -/

/-- A covering selection holds every label that is a strict maximum at some
probe. -/
theorem mem_of_readingCover_of_strict_max (slide : ℝ) (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} {peak : Fin 6} (probe : Fin 3 → ℝ)
    (hcover : ∃ good ∈ selected, ∀ label,
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
        ≤ point.mass good / point.weight good
          * (threeLinesDirection slide good ⬝ᵥ probe) ^ 2)
    (hstrict : ∀ label, label ≠ peak →
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
        < point.mass peak / point.weight peak
          * (threeLinesDirection slide peak ⬝ᵥ probe) ^ 2) :
    peak ∈ selected := by
  obtain ⟨good, hgoodMem, hgood⟩ := hcover
  by_cases hcase : good = peak
  · exact hcase ▸ hgoodMem
  · exact absurd (lt_of_lt_of_le (hstrict good hcase) (hgood peak)) (lt_irrefl _)

/-! ## The split family

The mean split is one member of a family.  Bounding the join by `(1 + 1 / split)`
and `(1 + split)` and paying at complementary shares gives a two-parameter cell
per join label, and the union over the two parameters is strictly larger than the
mean-split member. -/

/-- The parametric join bound.  The difference is a square over the parameter. -/
theorem sq_add_le_split (split x y : ℝ) (hsplit : 0 < split) :
    (x + y) ^ 2 ≤ (1 + 1 / split) * x ^ 2 + (1 + split) * y ^ 2 := by
  have hkey : (1 + 1 / split) * x ^ 2 + (1 + split) * y ^ 2 - (x + y) ^ 2
      = (x - split * y) ^ 2 / split := by
    field_simp
    ring
  have hpos : 0 ≤ (x - split * y) ^ 2 / split :=
    div_nonneg (sq_nonneg _) (le_of_lt hsplit)
  rw [← hkey] at hpos
  linarith

/-- The parametric bound for the sliding join. -/
theorem sq_add_smul_le_split (split slide y z : ℝ) (hsplit : 0 < split) :
    (y + slide * z) ^ 2 ≤ (1 + 1 / split) * y ^ 2 + (1 + split) * slide ^ 2 * z ^ 2 := by
  have hkey : (1 + 1 / split) * y ^ 2 + (1 + split) * slide ^ 2 * z ^ 2 - (y + slide * z) ^ 2
      = (y - split * slide * z) ^ 2 / split := by
    field_simp
    ring
  have hpos : 0 ≤ (y - split * slide * z) ^ 2 / split :=
    div_nonneg (sq_nonneg _) (le_of_lt hsplit)
  rw [← hkey] at hpos
  linarith

/-- The parametric bound for a difference join. -/
theorem sq_sub_le_split (split x y : ℝ) (hsplit : 0 < split) :
    (x - y) ^ 2 ≤ (1 + 1 / split) * x ^ 2 + (1 + split) * y ^ 2 := by
  have hrewrite : (x - y) ^ 2 = (x + -y) ^ 2 := by ring
  have hneg : (-y) ^ 2 = y ^ 2 := by ring
  rw [hrewrite]
  have := sq_add_le_split split x (-y) hsplit
  rw [hneg] at this
  exact this

/-! ## The K4 star cell

The K4 chart carries the SAME vertex-join incidence: labels `3`, `4`, `5` are the
three coordinate directions and labels `0`, `1`, `2` are their pairwise
DIFFERENCES.  So the pair-domination engine lands a second cell, on a second
registry obligation, with the star triple `{3,4,5}` in place of the vertex
triple.  That triple is one of the nine surviving spanning trees, so the cell
produces exactly what the knife band asks for. -/

/-- The K4 chart directions span: the last three are the coordinate axes. -/
theorem kFourDirection_span (probe : Fin 3 → ℝ)
    (hzero : ∀ label, kFourDirection label ⬝ᵥ probe = 0) : probe = 0 := by
  have hthree := hzero 3
  have hfour := hzero 4
  have hfive := hzero 5
  simp [kFourDirection_three, kFourDirection_four, kFourDirection_five,
    dotProduct, Fin.sum_univ_three] at hthree hfour hfive
  funext coordIndex
  fin_cases coordIndex
  · simpa using hthree
  · simpa using hfour
  · simpa using hfive

/-- The squared probe readings of the K4 chart, label by label. -/
theorem kFourDirection_dotProduct (probe : Fin 3 → ℝ) :
    kFourDirection 0 ⬝ᵥ probe = probe 0 - probe 1
      ∧ kFourDirection 1 ⬝ᵥ probe = probe 0 - probe 2
      ∧ kFourDirection 2 ⬝ᵥ probe = probe 1 - probe 2
      ∧ kFourDirection 3 ⬝ᵥ probe = probe 0
      ∧ kFourDirection 4 ⬝ᵥ probe = probe 1
      ∧ kFourDirection 5 ⬝ᵥ probe = probe 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [kFourDirection_zero, kFourDirection_one, kFourDirection_two,
      kFourDirection_three, kFourDirection_four, kFourDirection_five,
      dotProduct, Fin.sum_univ_three] <;> ring

/-- **The K4 star cell.**  Six inequalities paying each difference label against
the two coordinates it differs. -/
def KFourStarCoverCellFires (point : DirectionChartPoint 6) : Prop :=
  4 * (point.mass 0 / point.weight 0) ≤ point.mass 3 / point.weight 3
    ∧ 4 * (point.mass 0 / point.weight 0) ≤ point.mass 4 / point.weight 4
    ∧ 4 * (point.mass 1 / point.weight 1) ≤ point.mass 3 / point.weight 3
    ∧ 4 * (point.mass 1 / point.weight 1) ≤ point.mass 5 / point.weight 5
    ∧ 4 * (point.mass 2 / point.weight 2) ≤ point.mass 4 / point.weight 4
    ∧ 4 * (point.mass 2 / point.weight 2) ≤ point.mass 5 / point.weight 5

/-- **The K4 star cell forces the cover.** -/
theorem readingCover_starTriple_of_kFourCellFires (point : DirectionChartPoint 6)
    (hcell : KFourStarCoverCellFires point) :
    ∀ probe : Fin 3 → ℝ, ∃ good ∈ ({3, 4, 5} : Finset (Fin 6)), ∀ label,
      point.mass label / point.weight label * (kFourDirection label ⬝ᵥ probe) ^ 2
        ≤ point.mass good / point.weight good * (kFourDirection good ⬝ᵥ probe) ^ 2 := by
  obtain ⟨hzeroA, hzeroB, honeA, honeB, htwoA, htwoB⟩ := hcell
  intro probe
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := kFourDirection_dotProduct probe
  set kappa : Fin 6 → ℝ := fun label => point.mass label / point.weight label with hkappa
  have hkappaNonneg : ∀ label, 0 ≤ kappa label := fun label =>
    le_of_lt (div_pos (point.mass_pos label) (point.weight_pos label))
  set starA : ℝ := kappa 3 * probe 0 ^ 2 with hstarA
  set starB : ℝ := kappa 4 * probe 1 ^ 2 with hstarB
  set starC : ℝ := kappa 5 * probe 2 ^ 2 with hstarC
  have hsqA : (0 : ℝ) ≤ probe 0 ^ 2 := sq_nonneg _
  have hsqB : (0 : ℝ) ≤ probe 1 ^ 2 := sq_nonneg _
  have hsqC : (0 : ℝ) ≤ probe 2 ^ 2 := sq_nonneg _
  have hbound0 : kappa 0 * (probe 0 - probe 1) ^ 2 ≤ max starA starB :=
    reading_le_max_of_pairDomination (hkappaNonneg 0) hsqA hsqB
      (sq_sub_le_split 1 _ _ (by norm_num)) (by norm_num; linarith) (by norm_num; linarith)
  have hbound1 : kappa 1 * (probe 0 - probe 2) ^ 2 ≤ max starA starC :=
    reading_le_max_of_pairDomination (hkappaNonneg 1) hsqA hsqC
      (sq_sub_le_split 1 _ _ (by norm_num)) (by norm_num; linarith) (by norm_num; linarith)
  have hbound2 : kappa 2 * (probe 1 - probe 2) ^ 2 ≤ max starB starC :=
    reading_le_max_of_pairDomination (hkappaNonneg 2) hsqB hsqC
      (sq_sub_le_split 1 _ _ (by norm_num)) (by norm_num; linarith) (by norm_num; linarith)
  have hcase0 : kappa 0 * (kFourDirection 0 ⬝ᵥ probe) ^ 2 ≤ max starA (max starB starC) := by
    rw [hd0]; exact le_trans hbound0 (max_le le_max_three_left le_max_three_mid)
  have hcase1 : kappa 1 * (kFourDirection 1 ⬝ᵥ probe) ^ 2 ≤ max starA (max starB starC) := by
    rw [hd1]; exact le_trans hbound1 (max_le le_max_three_left le_max_three_right)
  have hcase2 : kappa 2 * (kFourDirection 2 ⬝ᵥ probe) ^ 2 ≤ max starA (max starB starC) := by
    rw [hd2]; exact le_trans hbound2 (max_le le_max_three_mid le_max_three_right)
  have hcase3 : kappa 3 * (kFourDirection 3 ⬝ᵥ probe) ^ 2 ≤ max starA (max starB starC) := by
    rw [hd3]; exact le_max_three_left
  have hcase4 : kappa 4 * (kFourDirection 4 ⬝ᵥ probe) ^ 2 ≤ max starA (max starB starC) := by
    rw [hd4]; exact le_max_three_mid
  have hcase5 : kappa 5 * (kFourDirection 5 ⬝ᵥ probe) ^ 2 ≤ max starA (max starB starC) := by
    rw [hd5]; exact le_max_three_right
  have hpeak : ∀ label, kappa label * (kFourDirection label ⬝ᵥ probe) ^ 2
      ≤ max starA (max starB starC) := by
    intro label
    fin_cases label
    · exact hcase0
    · exact hcase1
    · exact hcase2
    · exact hcase3
    · exact hcase4
    · exact hcase5
  rcases max_three_eq (a := starA) (b := starB) (c := starC) with heq | heq | heq
  · exact ⟨3, by decide, fun label => by rw [hd3]; exact le_trans (hpeak label) (le_of_eq heq)⟩
  · exact ⟨4, by decide, fun label => by rw [hd4]; exact le_trans (hpeak label) (le_of_eq heq)⟩
  · exact ⟨5, by decide, fun label => by rw [hd5]; exact le_trans (hpeak label) (le_of_eq heq)⟩

/-- **The K4 star cell fires.**  Six scalar inequalities give a strictly
dominating SPANNING TREE at the K4 chart point, with no minor, no determinant
and no invariant pencil. -/
theorem posDef_kFour_starTriple_of_cellFires (point : DirectionChartPoint 6)
    (hcell : KFourStarCoverCellFires point) :
    (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_of_readingCover kFourDirection point.mass point.weight
    point.mass_pos point.weight_pos point.weight_sum_one kFourDirection_span
    (by decide) (readingCover_starTriple_of_kFourCellFires point hcell)

/-- **The strict tree from the K4 star cell.** -/
theorem exists_posDef_kFour_of_starCoverCellFires (point : DirectionChartPoint 6)
    (hcell : KFourStarCoverCellFires point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection point.mass point.weight selected).PosDef :=
  ⟨{3, 4, 5}, by decide, posDef_kFour_starTriple_of_cellFires point hcell⟩

/-- The anti-diagonal probe of the first two coordinates. -/
def antiDiagonalProbe : Fin 3 → ℝ
  | 0 => 1
  | 1 => -1
  | 2 => 0

/-- **The K4 escape is exact.**  At the anti-diagonal probe the difference `0`
reads four times its kappa while the coordinates `3` and `4` read theirs once
and the coordinate `5` reads zero. -/
theorem not_readingCover_starTriple_of_difference_heavy (point : DirectionChartPoint 6)
    (hbeatThree : point.mass 3 / point.weight 3 < 4 * (point.mass 0 / point.weight 0))
    (hbeatFour : point.mass 4 / point.weight 4 < 4 * (point.mass 0 / point.weight 0)) :
    ¬ (∃ good ∈ ({3, 4, 5} : Finset (Fin 6)), ∀ label,
        point.mass label / point.weight label
            * (kFourDirection label ⬝ᵥ antiDiagonalProbe) ^ 2
          ≤ point.mass good / point.weight good
            * (kFourDirection good ⬝ᵥ antiDiagonalProbe) ^ 2) := by
  obtain ⟨hd0, _, _, hd3, hd4, hd5⟩ := kFourDirection_dotProduct antiDiagonalProbe
  have hp0 : antiDiagonalProbe 0 = 1 := rfl
  have hp1 : antiDiagonalProbe 1 = -1 := rfl
  have hp2 : antiDiagonalProbe 2 = 0 := rfl
  have hzeroPos : 0 < point.mass 0 / point.weight 0 :=
    div_pos (point.mass_pos 0) (point.weight_pos 0)
  rintro ⟨good, hgoodMem, hgood⟩
  have hdiff := hgood 0
  rw [hd0, hp0, hp1] at hdiff
  simp only [Finset.mem_insert, Finset.mem_singleton] at hgoodMem
  rcases hgoodMem with rfl | rfl | rfl
  · rw [hd3, hp0] at hdiff; norm_num at hdiff; linarith
  · rw [hd4, hp1] at hdiff; norm_num at hdiff; linarith
  · rw [hd5, hp2] at hdiff; norm_num at hdiff; linarith

/-! ## The split cover cell -/

/-- **The split cover cell.**  Six inequalities in the kappa ratios, the slide,
three split parameters and three shares. -/
def ThreeLinesSplitCoverCellFires (slide : ℝ) (point : DirectionChartPoint 6)
    (splitTwo shareTwo splitFour shareFour splitFive shareFive : ℝ) : Prop :=
  (1 + 1 / splitTwo) * (point.mass 2 / point.weight 2)
      ≤ shareTwo * (point.mass 0 / point.weight 0)
    ∧ (1 + splitTwo) * (point.mass 2 / point.weight 2)
      ≤ (1 - shareTwo) * (point.mass 1 / point.weight 1)
    ∧ (1 + 1 / splitFour) * (point.mass 4 / point.weight 4)
      ≤ shareFour * (point.mass 0 / point.weight 0)
    ∧ (1 + splitFour) * (point.mass 4 / point.weight 4)
      ≤ (1 - shareFour) * (point.mass 3 / point.weight 3)
    ∧ (1 + 1 / splitFive) * (point.mass 5 / point.weight 5)
      ≤ shareFive * (point.mass 1 / point.weight 1)
    ∧ (1 + splitFive) * slide ^ 2 * (point.mass 5 / point.weight 5)
      ≤ (1 - shareFive) * (point.mass 3 / point.weight 3)

/-- **The split cell forces the cover.** -/
theorem readingCover_vertexTriple_of_splitCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) {splitTwo shareTwo splitFour shareFour splitFive shareFive : ℝ}
    (hsplitTwo : 0 < splitTwo) (hshareTwoLow : 0 ≤ shareTwo) (hshareTwoHigh : shareTwo ≤ 1)
    (hsplitFour : 0 < splitFour) (hshareFourLow : 0 ≤ shareFour) (hshareFourHigh : shareFour ≤ 1)
    (hsplitFive : 0 < splitFive) (hshareFiveLow : 0 ≤ shareFive) (hshareFiveHigh : shareFive ≤ 1)
    (hcell : ThreeLinesSplitCoverCellFires slide point
      splitTwo shareTwo splitFour shareFour splitFive shareFive) :
    ∀ probe : Fin 3 → ℝ, ∃ good ∈ ({0, 1, 3} : Finset (Fin 6)), ∀ label,
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
        ≤ point.mass good / point.weight good
          * (threeLinesDirection slide good ⬝ᵥ probe) ^ 2 := by
  obtain ⟨hpayTwoA, hpayTwoB, hpayFourA, hpayFourB, hpayFiveA, hpayFiveB⟩ := hcell
  intro probe
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := threeLinesDirection_dotProduct slide probe
  set kappa : Fin 6 → ℝ := fun label => point.mass label / point.weight label with hkappa
  have hkappaNonneg : ∀ label, 0 ≤ kappa label := fun label =>
    le_of_lt (div_pos (point.mass_pos label) (point.weight_pos label))
  set vertexA : ℝ := kappa 0 * probe 0 ^ 2 with hvertexA
  set vertexB : ℝ := kappa 1 * probe 1 ^ 2 with hvertexB
  set vertexC : ℝ := kappa 3 * probe 2 ^ 2 with hvertexC
  have hsqA : (0 : ℝ) ≤ probe 0 ^ 2 := sq_nonneg _
  have hsqB : (0 : ℝ) ≤ probe 1 ^ 2 := sq_nonneg _
  have hsqC : (0 : ℝ) ≤ probe 2 ^ 2 := sq_nonneg _
  have hbound2 : kappa 2 * (probe 0 + probe 1) ^ 2 ≤ max vertexA vertexB :=
    reading_le_max_of_weightedPairDomination (hkappaNonneg 2) hsqA hsqB
      hshareTwoLow hshareTwoHigh (sq_add_le_split _ _ _ hsplitTwo)
      (by linarith) (by linarith)
  have hbound4 : kappa 4 * (probe 0 + probe 2) ^ 2 ≤ max vertexA vertexC :=
    reading_le_max_of_weightedPairDomination (hkappaNonneg 4) hsqA hsqC
      hshareFourLow hshareFourHigh (sq_add_le_split _ _ _ hsplitFour)
      (by linarith) (by linarith)
  have hbound5 : kappa 5 * (probe 1 + slide * probe 2) ^ 2 ≤ max vertexB vertexC :=
    reading_le_max_of_weightedPairDomination (hkappaNonneg 5) hsqB hsqC
      hshareFiveLow hshareFiveHigh (sq_add_smul_le_split _ _ _ _ hsplitFive)
      (by linarith) (by linarith)
  have hcase0 : kappa 0 * (threeLinesDirection slide 0 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by rw [hd0]; exact le_max_three_left
  have hcase1 : kappa 1 * (threeLinesDirection slide 1 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by rw [hd1]; exact le_max_three_mid
  have hcase2 : kappa 2 * (threeLinesDirection slide 2 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by
    rw [hd2]; exact le_trans hbound2 (max_le le_max_three_left le_max_three_mid)
  have hcase3 : kappa 3 * (threeLinesDirection slide 3 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by rw [hd3]; exact le_max_three_right
  have hcase4 : kappa 4 * (threeLinesDirection slide 4 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by
    rw [hd4]; exact le_trans hbound4 (max_le le_max_three_left le_max_three_right)
  have hcase5 : kappa 5 * (threeLinesDirection slide 5 ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by
    rw [hd5]; exact le_trans hbound5 (max_le le_max_three_mid le_max_three_right)
  have hpeak : ∀ label, kappa label * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
      ≤ max vertexA (max vertexB vertexC) := by
    intro label
    fin_cases label
    · exact hcase0
    · exact hcase1
    · exact hcase2
    · exact hcase3
    · exact hcase4
    · exact hcase5
  rcases max_three_eq (a := vertexA) (b := vertexB) (c := vertexC) with heq | heq | heq
  · exact ⟨0, by decide, fun label => by rw [hd0]; exact le_trans (hpeak label) (le_of_eq heq)⟩
  · exact ⟨1, by decide, fun label => by rw [hd1]; exact le_trans (hpeak label) (le_of_eq heq)⟩
  · exact ⟨3, by decide, fun label => by rw [hd3]; exact le_trans (hpeak label) (le_of_eq heq)⟩

/-- **The split cell fires.** -/
theorem posDef_threeLines_vertexTriple_of_splitCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) {splitTwo shareTwo splitFour shareFour splitFive shareFive : ℝ}
    (hsplitTwo : 0 < splitTwo) (hshareTwoLow : 0 ≤ shareTwo) (hshareTwoHigh : shareTwo ≤ 1)
    (hsplitFour : 0 < splitFour) (hshareFourLow : 0 ≤ shareFour) (hshareFourHigh : shareFour ≤ 1)
    (hsplitFive : 0 < splitFive) (hshareFiveLow : 0 ≤ shareFive) (hshareFiveHigh : shareFive ≤ 1)
    (hcell : ThreeLinesSplitCoverCellFires slide point
      splitTwo shareTwo splitFour shareFour splitFive shareFive) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef :=
  posDef_directionChartGap_threeLines_of_readingCover slide point (by decide)
    (readingCover_vertexTriple_of_splitCellFires slide point hsplitTwo hshareTwoLow
      hshareTwoHigh hsplitFour hshareFourLow hshareFourHigh hsplitFive hshareFiveLow
      hshareFiveHigh hcell)

/-- **The mean split is a member of the family.**  The factor-four cell is the
split cell at unit parameter and equal shares, so the family subsumes it. -/
theorem splitCellFires_of_cellFires (slide : ℝ) (point : DirectionChartPoint 6)
    (hcell : ThreeLinesVertexCoverCellFires slide point) :
    ThreeLinesSplitCoverCellFires slide point 1 (1 / 2) 1 (1 / 2) 1 (1 / 2) := by
  obtain ⟨hjoin2A, hjoin2B, hjoin4A, hjoin4B, hjoin5A, hjoin5B⟩ := hcell
  refine ⟨by norm_num; linarith, by norm_num; linarith, by norm_num; linarith,
    by norm_num; linarith, by norm_num; linarith, ?_⟩
  have hrewrite : (1 + 1) * slide ^ 2 * (point.mass 5 / point.weight 5)
      = (4 * slide ^ 2 * (point.mass 5 / point.weight 5)) / 2 := by ring
  rw [hrewrite]
  norm_num
  linarith

/-! ## The axis probes force the vertex triple -/

/-- **The first axis forces the vertex `0`.**  It sees `{0, 2, 4}` with unit
squared readings. -/
theorem firstAxis_forces_vertexZero (slide : ℝ) (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)}
    (hbeatTwo : point.mass 2 / point.weight 2 < point.mass 0 / point.weight 0)
    (hbeatFour : point.mass 4 / point.weight 4 < point.mass 0 / point.weight 0)
    (hcover : ∃ good ∈ selected, ∀ label,
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ firstAxisProbe) ^ 2
        ≤ point.mass good / point.weight good
          * (threeLinesDirection slide good ⬝ᵥ firstAxisProbe) ^ 2) :
    (0 : Fin 6) ∈ selected := by
  refine mem_of_readingCover_of_strict_max slide point firstAxisProbe hcover ?_
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := threeLinesDirection_dotProduct slide firstAxisProbe
  have hp0 : firstAxisProbe 0 = 1 := rfl
  have hp1 : firstAxisProbe 1 = 0 := rfl
  have hp2 : firstAxisProbe 2 = 0 := rfl
  have hzeroPos : 0 < point.mass 0 / point.weight 0 :=
    div_pos (point.mass_pos 0) (point.weight_pos 0)
  have hrhs : point.mass 0 / point.weight 0
      * (threeLinesDirection slide 0 ⬝ᵥ firstAxisProbe) ^ 2
      = point.mass 0 / point.weight 0 := by rw [hd0, hp0]; ring
  have hone : point.mass 1 / point.weight 1
      * (threeLinesDirection slide 1 ⬝ᵥ firstAxisProbe) ^ 2
      < point.mass 0 / point.weight 0 := by rw [hd1, hp1]; simpa using hzeroPos
  have htwo : point.mass 2 / point.weight 2
      * (threeLinesDirection slide 2 ⬝ᵥ firstAxisProbe) ^ 2
      < point.mass 0 / point.weight 0 := by rw [hd2, hp0, hp1]; simpa using hbeatTwo
  have hthree : point.mass 3 / point.weight 3
      * (threeLinesDirection slide 3 ⬝ᵥ firstAxisProbe) ^ 2
      < point.mass 0 / point.weight 0 := by rw [hd3, hp2]; simpa using hzeroPos
  have hfour : point.mass 4 / point.weight 4
      * (threeLinesDirection slide 4 ⬝ᵥ firstAxisProbe) ^ 2
      < point.mass 0 / point.weight 0 := by rw [hd4, hp0, hp2]; simpa using hbeatFour
  have hfive : point.mass 5 / point.weight 5
      * (threeLinesDirection slide 5 ⬝ᵥ firstAxisProbe) ^ 2
      < point.mass 0 / point.weight 0 := by rw [hd5, hp1, hp2]; simpa using hzeroPos
  intro label hne
  rw [hrhs]
  fin_cases label
  · exact absurd rfl hne
  · exact hone
  · exact htwo
  · exact hthree
  · exact hfour
  · exact hfive

/-- **The second axis forces the vertex `1`.**  It sees `{1, 2, 5}`. -/
theorem secondAxis_forces_vertexOne (slide : ℝ) (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)}
    (hbeatTwo : point.mass 2 / point.weight 2 < point.mass 1 / point.weight 1)
    (hbeatFive : point.mass 5 / point.weight 5 < point.mass 1 / point.weight 1)
    (hcover : ∃ good ∈ selected, ∀ label,
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ secondAxisProbe) ^ 2
        ≤ point.mass good / point.weight good
          * (threeLinesDirection slide good ⬝ᵥ secondAxisProbe) ^ 2) :
    (1 : Fin 6) ∈ selected := by
  refine mem_of_readingCover_of_strict_max slide point secondAxisProbe hcover ?_
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := threeLinesDirection_dotProduct slide secondAxisProbe
  have hp0 : secondAxisProbe 0 = 0 := rfl
  have hp1 : secondAxisProbe 1 = 1 := rfl
  have hp2 : secondAxisProbe 2 = 0 := rfl
  have honePos : 0 < point.mass 1 / point.weight 1 :=
    div_pos (point.mass_pos 1) (point.weight_pos 1)
  have hrhs : point.mass 1 / point.weight 1
      * (threeLinesDirection slide 1 ⬝ᵥ secondAxisProbe) ^ 2
      = point.mass 1 / point.weight 1 := by rw [hd1, hp1]; ring
  have hzero : point.mass 0 / point.weight 0
      * (threeLinesDirection slide 0 ⬝ᵥ secondAxisProbe) ^ 2
      < point.mass 1 / point.weight 1 := by rw [hd0, hp0]; simpa using honePos
  have htwo : point.mass 2 / point.weight 2
      * (threeLinesDirection slide 2 ⬝ᵥ secondAxisProbe) ^ 2
      < point.mass 1 / point.weight 1 := by rw [hd2, hp0, hp1]; simpa using hbeatTwo
  have hthree : point.mass 3 / point.weight 3
      * (threeLinesDirection slide 3 ⬝ᵥ secondAxisProbe) ^ 2
      < point.mass 1 / point.weight 1 := by rw [hd3, hp2]; simpa using honePos
  have hfour : point.mass 4 / point.weight 4
      * (threeLinesDirection slide 4 ⬝ᵥ secondAxisProbe) ^ 2
      < point.mass 1 / point.weight 1 := by rw [hd4, hp0, hp2]; simpa using honePos
  have hfive : point.mass 5 / point.weight 5
      * (threeLinesDirection slide 5 ⬝ᵥ secondAxisProbe) ^ 2
      < point.mass 1 / point.weight 1 := by rw [hd5, hp1, hp2]; simpa using hbeatFive
  intro label hne
  rw [hrhs]
  fin_cases label
  · exact hzero
  · exact absurd rfl hne
  · exact htwo
  · exact hthree
  · exact hfour
  · exact hfive

/-- **The vertical axis forces the vertex `3`.**  It sees `{3, 4, 5}`, and the
slide enters squared on the sliding label. -/
theorem verticalAxis_forces_vertexThree (slide : ℝ) (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)}
    (hbeatFour : point.mass 4 / point.weight 4 < point.mass 3 / point.weight 3)
    (hbeatFive : slide ^ 2 * (point.mass 5 / point.weight 5)
      < point.mass 3 / point.weight 3)
    (hcover : ∃ good ∈ selected, ∀ label,
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ verticalProbe) ^ 2
        ≤ point.mass good / point.weight good
          * (threeLinesDirection slide good ⬝ᵥ verticalProbe) ^ 2) :
    (3 : Fin 6) ∈ selected := by
  refine mem_of_readingCover_of_strict_max slide point verticalProbe hcover ?_
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := threeLinesDirection_dotProduct slide verticalProbe
  have hp0 : verticalProbe 0 = 0 := rfl
  have hp1 : verticalProbe 1 = 0 := rfl
  have hp2 : verticalProbe 2 = 1 := rfl
  have hthreePos : 0 < point.mass 3 / point.weight 3 :=
    div_pos (point.mass_pos 3) (point.weight_pos 3)
  have hrhs : point.mass 3 / point.weight 3
      * (threeLinesDirection slide 3 ⬝ᵥ verticalProbe) ^ 2
      = point.mass 3 / point.weight 3 := by rw [hd3, hp2]; ring
  have hzero : point.mass 0 / point.weight 0
      * (threeLinesDirection slide 0 ⬝ᵥ verticalProbe) ^ 2
      < point.mass 3 / point.weight 3 := by rw [hd0, hp0]; simpa using hthreePos
  have hone : point.mass 1 / point.weight 1
      * (threeLinesDirection slide 1 ⬝ᵥ verticalProbe) ^ 2
      < point.mass 3 / point.weight 3 := by rw [hd1, hp1]; simpa using hthreePos
  have htwo : point.mass 2 / point.weight 2
      * (threeLinesDirection slide 2 ⬝ᵥ verticalProbe) ^ 2
      < point.mass 3 / point.weight 3 := by rw [hd2, hp0, hp1]; simpa using hthreePos
  have hfour : point.mass 4 / point.weight 4
      * (threeLinesDirection slide 4 ⬝ᵥ verticalProbe) ^ 2
      < point.mass 3 / point.weight 3 := by rw [hd4, hp0, hp2]; simpa using hbeatFour
  have hfive : point.mass 5 / point.weight 5
      * (threeLinesDirection slide 5 ⬝ᵥ verticalProbe) ^ 2
      < point.mass 3 / point.weight 3 := by
    rw [hd5, hp1, hp2]
    have hshape : point.mass 5 / point.weight 5 * (0 + slide * 1) ^ 2
        = slide ^ 2 * (point.mass 5 / point.weight 5) := by ring
    rw [hshape]; exact hbeatFive
  intro label hne
  rw [hrhs]
  fin_cases label
  · exact hzero
  · exact hone
  · exact htwo
  · exact absurd rfl hne
  · exact hfour
  · exact hfive

/-- **The forced triple.**  Under the six strict axis conditions a card-three
covering selection is exactly the vertex triple. -/
theorem readingCover_eq_vertexTriple_of_axisStrict (slide : ℝ)
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    (hcard : selected.card = 3)
    (hzeroTwo : point.mass 2 / point.weight 2 < point.mass 0 / point.weight 0)
    (hzeroFour : point.mass 4 / point.weight 4 < point.mass 0 / point.weight 0)
    (honeTwo : point.mass 2 / point.weight 2 < point.mass 1 / point.weight 1)
    (honeFive : point.mass 5 / point.weight 5 < point.mass 1 / point.weight 1)
    (hthreeFour : point.mass 4 / point.weight 4 < point.mass 3 / point.weight 3)
    (hthreeFive : slide ^ 2 * (point.mass 5 / point.weight 5)
      < point.mass 3 / point.weight 3)
    (hcover : ∀ probe : Fin 3 → ℝ, ∃ good ∈ selected, ∀ label,
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
        ≤ point.mass good / point.weight good
          * (threeLinesDirection slide good ⬝ᵥ probe) ^ 2) :
    selected = ({0, 1, 3} : Finset (Fin 6)) := by
  have hzeroMem : (0 : Fin 6) ∈ selected :=
    firstAxis_forces_vertexZero slide point hzeroTwo hzeroFour (hcover firstAxisProbe)
  have honeMem : (1 : Fin 6) ∈ selected :=
    secondAxis_forces_vertexOne slide point honeTwo honeFive (hcover secondAxisProbe)
  have hthreeMem : (3 : Fin 6) ∈ selected :=
    verticalAxis_forces_vertexThree slide point hthreeFour hthreeFive (hcover verticalProbe)
  have hsubset : ({0, 1, 3} : Finset (Fin 6)) ⊆ selected := by
    intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl | rfl
    · exact hzeroMem
    · exact honeMem
    · exact hthreeMem
  exact (Finset.eq_of_subset_of_card_le hsubset (by rw [hcard]; decide)).symm

/-- **THE BLINDNESS KILL.**  Under the six strict axis conditions the covering
triple is forced to be the vertex triple, and the diagonal probe then refutes it
as soon as four times `kappa_2` beats both vertex ratios.  So in that region NO
card-three selection satisfies the covering criterion: the reading-cover cell is
BLIND there rather than merely unfired, and no further probe can rescue it. -/
theorem not_exists_readingCover_of_axisStrict_of_join_heavy (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hzeroTwo : point.mass 2 / point.weight 2 < point.mass 0 / point.weight 0)
    (hzeroFour : point.mass 4 / point.weight 4 < point.mass 0 / point.weight 0)
    (honeTwo : point.mass 2 / point.weight 2 < point.mass 1 / point.weight 1)
    (honeFive : point.mass 5 / point.weight 5 < point.mass 1 / point.weight 1)
    (hthreeFour : point.mass 4 / point.weight 4 < point.mass 3 / point.weight 3)
    (hthreeFive : slide ^ 2 * (point.mass 5 / point.weight 5)
      < point.mass 3 / point.weight 3)
    (hbeatFirst : point.mass 0 / point.weight 0 < 4 * (point.mass 2 / point.weight 2))
    (hbeatSecond : point.mass 1 / point.weight 1 < 4 * (point.mass 2 / point.weight 2)) :
    ¬ (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        ∀ probe : Fin 3 → ℝ, ∃ good ∈ selected, ∀ label,
          point.mass label / point.weight label
              * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
            ≤ point.mass good / point.weight good
              * (threeLinesDirection slide good ⬝ᵥ probe) ^ 2) := by
  rintro ⟨selected, hcard, hcover⟩
  have hforced : selected = ({0, 1, 3} : Finset (Fin 6)) :=
    readingCover_eq_vertexTriple_of_axisStrict slide point hcard hzeroTwo hzeroFour
      honeTwo honeFive hthreeFour hthreeFive hcover
  subst hforced
  exact not_readingCover_vertexTriple_of_join_heavy slide point hbeatFirst hbeatSecond
    (hcover diagonalProbe)

end Gtz
