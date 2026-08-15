import Gtz.Design.StarCorankClosure
import Gtz.Wave.KFourRowCertificateWiring
import Gtz.Reduction.ConnectednessRouteCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The star-wall vacuity: the family coordinates and the balanced case

The gauge-star corank-two wall is an explicit rational family.  This module
lands the family coordinates and the first proved case of the vacuity target.

* `kFourGaugeStarWall_positive_axis` — the wall normal form with the axis
  entrywise positive: the sign flip is free because the atom of `-z` is the
  atom of `z`.
* `kFourGaugeStarWall_family` — the six division-free wall equations: the
  three triangle masses are the scaled pairwise axis products, and the three
  tree boost identities pin the on-tree mass-weight ratios.
* `kFourStarACell_fires_of_wall_balanced` — the balanced case: when the first
  axis coordinate is maximal and the four weights that the vertex-a star reads
  are at most one sixth, the star-a cell fires.  The determinant bound has a
  slack factor near three, so every inequality is a product chain.
* `kFourAtlas_fires_of_wall_balanced` — the assembly into the vacuity target's
  conclusion: the balanced wall case fires the full minor atlas.

The probe map behind the case selection: at 52000 exact wall samples the
atlas never fails, the three vertex stars carry every one-cell tight point,
and the star cover misses only a thin stratum where one triangle edge and one
tree edge at a common triangle vertex are simultaneously heavy.
-/

namespace Gtz

open Matrix

/-! ## 1. The positive-axis normal form -/

/-- The wall normal form with an entrywise positive axis.  The landed normal
form gives positive pairwise products; the atom is blind to the global sign
flip, so the axis is choosable positive. -/
theorem kFourGaugeStarWall_positive_axis (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hdata : KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6))) :
    ∃ (axis : Fin 3 → ℝ) (scale : ℝ),
      directionChartGap kFourDirection point.mass point.weight
          ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis ∧
      0 < scale ∧ 0 < axis 0 ∧ 0 < axis 1 ∧ 0 < axis 2 := by
  obtain ⟨axis, scale, heq, hscale, h01, h02, h12⟩ :=
    kFourGaugeStar_corankTwo_normalForm point hpsd hdata
  rcases mul_pos_iff.mp h01 with ⟨ha0, ha1⟩ | ⟨ha0, ha1⟩
  · have ha2 : 0 < axis 2 := by
      rcases mul_pos_iff.mp h02 with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd ha0 (not_lt.mpr h.le)
    exact ⟨axis, scale, heq, hscale, ha0, ha1, ha2⟩
  · have ha2 : axis 2 < 0 := by
      rcases mul_pos_iff.mp h02 with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h (not_lt.mpr ha0.le)
      · exact h
    refine ⟨-axis, scale, ?_, hscale, ?_, ?_, ?_⟩
    · rw [atomMatrix_neg]
      exact heq
    · simpa using neg_pos.mpr ha0
    · simpa using neg_pos.mpr ha1
    · simpa using neg_pos.mpr ha2

/-! ## 2. The six wall equations -/

/-- **The wall family.**  At a gauge-star corank-two wall point the six chart
quantities are pinned by a positive axis and a positive scale: the triangle
masses are the scaled pairwise products, and the tree boost identities hold in
division-free form. -/
theorem kFourGaugeStarWall_family (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hdata : KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6))) :
    ∃ (z : Fin 3 → ℝ) (s : ℝ),
      0 < z 0 ∧ 0 < z 1 ∧ 0 < z 2 ∧ 0 < s ∧
      point.mass 0 = s * (z 0 * z 1) ∧
      point.mass 1 = s * (z 0 * z 2) ∧
      point.mass 2 = s * (z 1 * z 2) ∧
      point.mass 3 * (1 - point.weight 3)
        = s * (z 0 * (z 0 + z 1 + z 2)) * point.weight 3 ∧
      point.mass 4 * (1 - point.weight 4)
        = s * (z 1 * (z 0 + z 1 + z 2)) * point.weight 4 ∧
      point.mass 5 * (1 - point.weight 5)
        = s * (z 2 * (z 0 + z 1 + z 2)) * point.weight 5 := by
  obtain ⟨z, s, heq, hs, hz0, hz1, hz2⟩ :=
    kFourGaugeStarWall_positive_axis point hpsd hdata
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := kFourCoeff_eq_of_rankOne heq
  have hmem3 : (3 : Fin 6) ∈ ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hmem4 : (4 : Fin 6) ∈ ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hmem5 : (5 : Fin 6) ∈ ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hnot0 : (0 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hnot1 : (1 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6)) := by decide
  have hnot2 : (2 : Fin 6) ∉ ({3, 4, 5} : Finset (Fin 6)) := by decide
  rw [chartCoeff, if_neg hnot0] at c0
  rw [chartCoeff, if_neg hnot1] at c1
  rw [chartCoeff, if_neg hnot2] at c2
  rw [chartCoeff, if_pos hmem3] at c3
  rw [chartCoeff, if_pos hmem4] at c4
  rw [chartCoeff, if_pos hmem5] at c5
  refine ⟨z, s, hz0, hz1, hz2, hs, by linarith, by linarith, by linarith,
    ?_, ?_, ?_⟩
  · have hw := point.weight_pos 3
    have hdiv : point.mass 3 / point.weight 3
        = s * (z 0 * (z 0 + z 1 + z 2)) + point.mass 3 := by linarith
    rw [div_eq_iff hw.ne'] at hdiv
    nlinarith [hdiv]
  · have hw := point.weight_pos 4
    have hdiv : point.mass 4 / point.weight 4
        = s * (z 1 * (z 0 + z 1 + z 2)) + point.mass 4 := by linarith
    rw [div_eq_iff hw.ne'] at hdiv
    nlinarith [hdiv]
  · have hw := point.weight_pos 5
    have hdiv : point.mass 5 / point.weight 5
        = s * (z 2 * (z 0 + z 1 + z 2)) + point.mass 5 := by linarith
    rw [div_eq_iff hw.ne'] at hdiv
    nlinarith [hdiv]

/-! ## 3. The balanced case at the vertex-a star -/

/-- **The balanced case.**  On the wall family with the first axis coordinate
maximal, if the four weights read by the vertex-a star are at most one sixth,
the star-a cell fires.  The floors are five times the two triangle masses and
the exact third boost. -/
theorem kFourStarACell_fires_of_wall_balanced (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s : ℝ}
    (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hz2 : 0 < z 2) (hs : 0 < s)
    (hm0 : point.mass 0 = s * (z 0 * z 1))
    (hm1 : point.mass 1 = s * (z 0 * z 2))
    (hm2 : point.mass 2 = s * (z 1 * z 2))
    (hd3 : point.mass 3 * (1 - point.weight 3)
      = s * (z 0 * (z 0 + z 1 + z 2)) * point.weight 3)
    (hd4 : point.mass 4 * (1 - point.weight 4)
      = s * (z 1 * (z 0 + z 1 + z 2)) * point.weight 4)
    (hd5 : point.mass 5 * (1 - point.weight 5)
      = s * (z 2 * (z 0 + z 1 + z 2)) * point.weight 5)
    (hmax1 : z 1 ≤ z 0) (hmax2 : z 2 ≤ z 0)
    (hw0 : 6 * point.weight 0 ≤ 1) (hw1 : 6 * point.weight 1 ≤ 1)
    (hw4 : 6 * point.weight 4 ≤ 1) (hw5 : 6 * point.weight 5 ≤ 1) :
    KFourUnsignedStarACellFires point := by
  have hw0pos := point.weight_pos 0
  have hw1pos := point.weight_pos 1
  have hw4pos := point.weight_pos 4
  have hw5pos := point.weight_pos 5
  have hm4pos := point.mass_pos 4
  have hm5pos := point.mass_pos 5
  -- the two demand caps: five times the on-tree mass is below the boost
  have hcap4 : 5 * point.mass 4 ≤ s * (z 1 * (z 0 + z 1 + z 2)) := by
    have hstep : (5 * point.mass 4) * point.weight 4
        ≤ (s * (z 1 * (z 0 + z 1 + z 2))) * point.weight 4 := by
      nlinarith [hd4, hm4pos]
    exact le_of_mul_le_mul_right hstep hw4pos
  have hcap5 : 5 * point.mass 5 ≤ s * (z 2 * (z 0 + z 1 + z 2)) := by
    have hstep : (5 * point.mass 5) * point.weight 5
        ≤ (s * (z 2 * (z 0 + z 1 + z 2))) * point.weight 5 := by
      nlinarith [hd5, hm5pos]
    exact le_of_mul_le_mul_right hstep hw5pos
  refine ⟨5 * (s * (z 0 * z 1)), 5 * (s * (z 0 * z 2)),
    s * (z 0 * (z 0 + z 1 + z 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm0]
    nlinarith [mul_pos hs (mul_pos hz0 hz1)]
  · rw [hm1]
    nlinarith [mul_pos hs (mul_pos hz0 hz2)]
  · rw [hd3]
  · -- the corner: 25 z0 beats 5 z2 + sigma against the z1 row
    rw [hm2]
    nlinarith [hcap4, mul_pos (mul_pos hs hz1) hz0,
      mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz1).le,
      mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz1).le]
  · -- the second minor: the product of the two corner floors beats the
    -- squared triangle mass
    rw [hm2]
    have hA : 17 / 5 * (s * (z 0 * z 1))
        ≤ 5 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4) := by
      nlinarith [hcap4, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz1).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz1).le]
    have hB : 17 / 5 * (s * (z 0 * z 2))
        ≤ 5 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5) := by
      nlinarith [hcap5, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz2).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz2).le]
    have hApos : 0 < 17 / 5 * (s * (z 0 * z 1)) := by positivity
    have hBpos : 0 < 17 / 5 * (s * (z 0 * z 2)) := by positivity
    have hprod : (17 / 5 * (s * (z 0 * z 1))) * (17 / 5 * (s * (z 0 * z 2)))
        ≤ (5 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4))
          * (5 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5)) :=
      mul_le_mul hA hB hBpos.le (le_trans hApos.le hA)
    nlinarith [hprod, mul_le_mul hmax1 hmax2 hz2.le hz0.le,
      mul_pos (mul_pos hs hs) (mul_pos hz1 hz2),
      mul_pos (mul_pos (mul_pos hs hs) (mul_pos hz1 hz2)) (mul_pos hz0 hz0)]
  · -- the determinant: the slack factor is near three, and every term is a
    -- product of the established caps
    rw [hm2]
    set sg := z 0 + z 1 + z 2 with hsg
    have hsgpos : 0 < sg := by rw [hsg]; linarith
    have hsgle : sg ≤ 3 * z 0 := by rw [hsg]; linarith
    have hA : 17 / 5 * (s * (z 0 * z 1))
        ≤ 5 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4) := by
      nlinarith [hcap4, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz1).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz1).le]
    have hB : 17 / 5 * (s * (z 0 * z 2))
        ≤ 5 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5) := by
      nlinarith [hcap5, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz2).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz2).le]
    have hC : 3 / 5 * (s * (z 0 * sg))
        ≤ s * (z 0 * sg) - (point.mass 4 + point.mass 5) := by
      nlinarith [hcap4, hcap5,
        mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hsgpos).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hsgpos).le,
        mul_pos hs (mul_pos hz0 hsgpos)]
    have hAup : 5 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4)
        ≤ 5 * (s * (z 0 * z 1)) := by
      nlinarith [mul_pos hs (mul_pos hz1 hz2), hm4pos]
    have hBup : 5 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5)
        ≤ 5 * (s * (z 0 * z 2)) := by
      nlinarith [mul_pos hs (mul_pos hz1 hz2), hm5pos]
    have hCup : s * (z 0 * sg) - (point.mass 4 + point.mass 5)
        ≤ s * (z 0 * sg) := by nlinarith [hm4pos, hm5pos]
    have hApos : 0 < 17 / 5 * (s * (z 0 * z 1)) := by positivity
    have hBpos : 0 < 17 / 5 * (s * (z 0 * z 2)) := by positivity
    have hCpos : 0 < 3 / 5 * (s * (z 0 * sg)) := by positivity
    set aa := 5 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4) with haa
    set bb := 5 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5) with hbb
    set cc := s * (z 0 * sg) - (point.mass 4 + point.mass 5) with hcc
    have haapos : 0 < aa := lt_of_lt_of_le hApos hA
    have hbbpos : 0 < bb := lt_of_lt_of_le hBpos hB
    have hccpos : 0 < cc := lt_of_lt_of_le hCpos hC
    -- the five term bounds
    have habc : (17 / 5 * (s * (z 0 * z 1))) * (17 / 5 * (s * (z 0 * z 2)))
        * (3 / 5 * (s * (z 0 * sg))) ≤ aa * bb * cc := by
      have h1 : (17 / 5 * (s * (z 0 * z 1))) * (17 / 5 * (s * (z 0 * z 2)))
          ≤ aa * bb := mul_le_mul hA hB hBpos.le haapos.le
      exact mul_le_mul h1 hC hCpos.le (mul_nonneg haapos.le hbbpos.le)
    have hR2 : point.mass 5 ^ 2 ≤ (s * (z 2 * sg) / 5) ^ 2 := by
      have h5 : point.mass 5 ≤ s * (z 2 * sg) / 5 := by linarith
      nlinarith [mul_self_le_mul_self hm5pos.le h5]
    have hQ2 : point.mass 4 ^ 2 ≤ (s * (z 1 * sg) / 5) ^ 2 := by
      have h4 : point.mass 4 ≤ s * (z 1 * sg) / 5 := by linarith
      nlinarith [mul_self_le_mul_self hm4pos.le h4]
    have haR2 : aa * point.mass 5 ^ 2
        ≤ 5 * (s * (z 0 * z 1)) * ((s * (z 2 * sg) / 5) ^ 2) := by
      have := mul_le_mul hAup hR2 (sq_nonneg (point.mass 5)) (by positivity)
      linarith
    have hbQ2 : point.mass 4 ^ 2 * bb
        ≤ (s * (z 1 * sg) / 5) ^ 2 * (5 * (s * (z 0 * z 2))) := by
      have := mul_le_mul hQ2 hBup hbbpos.le (by positivity)
      linarith
    have hcP2 : (s * (z 1 * z 2)) ^ 2 * cc
        ≤ (s * (z 1 * z 2)) ^ 2 * (s * (z 0 * sg)) := by
      have := mul_le_mul_of_nonneg_left hCup (sq_nonneg (s * (z 1 * z 2)))
      linarith
    have hPQR : 2 * (s * (z 1 * z 2)) * point.mass 4 * point.mass 5
        ≤ 2 * (s * (z 1 * z 2)) * (s * (z 1 * sg) / 5) * (s * (z 2 * sg) / 5) := by
      have h4 : point.mass 4 ≤ s * (z 1 * sg) / 5 := by linarith
      have h5 : point.mass 5 ≤ s * (z 2 * sg) / 5 := by linarith
      have hP2 : 0 < 2 * (s * (z 1 * z 2)) := by positivity
      have hstep : 2 * (s * (z 1 * z 2)) * point.mass 4
          ≤ 2 * (s * (z 1 * z 2)) * (s * (z 1 * sg) / 5) :=
        mul_le_mul_of_nonneg_left h4 hP2.le
      calc 2 * (s * (z 1 * z 2)) * point.mass 4 * point.mass 5
          ≤ 2 * (s * (z 1 * z 2)) * (s * (z 1 * sg) / 5) * point.mass 5 :=
            mul_le_mul_of_nonneg_right hstep hm5pos.le
        _ ≤ 2 * (s * (z 1 * z 2)) * (s * (z 1 * sg) / 5)
              * (s * (z 2 * sg) / 5) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
    -- the closing comparison: each negative term is bounded by a rational
    -- multiple of the master monomial `s^3 z0^3 z1 z2 sg`
    have hXpos : 0 < s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))
        := by positivity
    have hz2sg : z 2 * sg ≤ 3 * (z 0 * z 0) := by nlinarith [hmax2, hsgle]
    have hz1sg : z 1 * sg ≤ 3 * (z 0 * z 0) := by nlinarith [hmax1, hsgle]
    have hz12 : z 1 * z 2 ≤ z 0 * z 0 :=
      mul_le_mul hmax1 hmax2 hz2.le hz0.le
    have hT1 : 5 * (s * (z 0 * z 1)) * ((s * (z 2 * sg) / 5) ^ 2)
        ≤ 3 / 5 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz2sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz0.le hz1.le)
            (mul_nonneg hz2.le hsgpos.le)))]
    have hT2 : (s * (z 1 * sg) / 5) ^ 2 * (5 * (s * (z 0 * z 2)))
        ≤ 3 / 5 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz1sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz0.le hz2.le)
            (mul_nonneg hz1.le hsgpos.le)))]
    have hT3 : (s * (z 1 * z 2)) ^ 2 * (s * (z 0 * sg))
        ≤ 1 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz12
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz0.le hsgpos.le)
            (mul_nonneg hz1.le hz2.le)))]
    have hT4 : 2 * (s * (z 1 * z 2)) * (s * (z 1 * sg) / 5) * (s * (z 2 * sg) / 5)
        ≤ 6 / 25 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
      have hz12sg : z 1 * z 2 * sg ≤ z 0 * z 0 * (3 * z 0) := by
        nlinarith [mul_le_mul_of_nonneg_left hsgle (mul_nonneg hz1.le hz2.le),
          mul_le_mul_of_nonneg_right hz12 hsgpos.le]
      nlinarith [mul_le_mul_of_nonneg_left hz12sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz1.le hz2.le) hsgpos.le))]
    have hRHS : (17 / 5 * (s * (z 0 * z 1))) * (17 / 5 * (s * (z 0 * z 2)))
          * (3 / 5 * (s * (z 0 * sg)))
        = 867 / 125 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
      ring
    have hMain : 867 / 125
          * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg))))
        ≤ aa * bb * cc := hRHS ▸ habc
    have hN1 : aa * point.mass 5 ^ 2
        ≤ 3 / 5 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) :=
      le_trans haR2 hT1
    have hN2 : point.mass 4 ^ 2 * bb
        ≤ 3 / 5 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) :=
      le_trans hbQ2 hT2
    have hN3 : (s * (z 1 * z 2)) ^ 2 * cc
        ≤ 1 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) :=
      le_trans hcP2 hT3
    have hN4 : 2 * (s * (z 1 * z 2)) * point.mass 4 * point.mass 5
        ≤ 6 / 25 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) :=
      le_trans hPQR hT4
    linarith [hMain, hN1, hN2, hN3, hN4, hXpos]

/-! ## 4. The assembly into the atlas -/

/-- The balanced wall case fires the full minor atlas. -/
theorem kFourAtlas_fires_of_wall_balanced (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s : ℝ}
    (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hz2 : 0 < z 2) (hs : 0 < s)
    (hm0 : point.mass 0 = s * (z 0 * z 1))
    (hm1 : point.mass 1 = s * (z 0 * z 2))
    (hm2 : point.mass 2 = s * (z 1 * z 2))
    (hd3 : point.mass 3 * (1 - point.weight 3)
      = s * (z 0 * (z 0 + z 1 + z 2)) * point.weight 3)
    (hd4 : point.mass 4 * (1 - point.weight 4)
      = s * (z 1 * (z 0 + z 1 + z 2)) * point.weight 4)
    (hd5 : point.mass 5 * (1 - point.weight 5)
      = s * (z 2 * (z 0 + z 1 + z 2)) * point.weight 5)
    (hmax1 : z 1 ≤ z 0) (hmax2 : z 2 ≤ z 0)
    (hw0 : 6 * point.weight 0 ≤ 1) (hw1 : 6 * point.weight 1 ≤ 1)
    (hw4 : 6 * point.weight 4 ≤ 1) (hw5 : 6 * point.weight 5 ≤ 1) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inl
    (kFourStarACell_fires_of_wall_balanced point hz0 hz1 hz2 hs hm0 hm1 hm2
      hd3 hd4 hd5 hmax1 hmax2 hw0 hw1 hw4 hw5)))))

end Gtz
