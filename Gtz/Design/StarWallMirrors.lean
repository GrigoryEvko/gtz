import Gtz.Design.StarWallVacuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The star-wall mirrors: the balanced cases at the vertex-b and vertex-c stars

The landed balanced case fires the vertex-a star when the first axis
coordinate is maximal.  This module lands the two mirrors.

* `kFourStarBCell_fires_of_wall_balanced` — the vertex-b star fires when the
  second axis coordinate is maximal and the four weights that the star reads
  are at most one sixth.
* `kFourStarCCell_fires_of_wall_balanced` — the vertex-c star, third
  coordinate maximal, same weight bounds.
* The two assemblies into the full minor atlas.

With the landed vertex-a case the balanced regime is complete: at every wall
point whose maximal axis coordinate has its star's four weights at most one
sixth, the atlas fires.  The heavy regimes and the aligned-pair stratum
remain, with their exact case map in the probe data.
-/

namespace Gtz

open Matrix

/-! ## 1. The vertex-b mirror -/

/-- **The balanced case at the vertex-b star.**  On the wall family with the
second axis coordinate maximal, if the four weights read by the vertex-b star
are at most one sixth, the star-b cell fires. -/
theorem kFourStarBCell_fires_of_wall_balanced (point : DirectionChartPoint 6)
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
    (hmax0 : z 0 ≤ z 1) (hmax2 : z 2 ≤ z 1)
    (hw0 : 6 * point.weight 0 ≤ 1) (hw2 : 6 * point.weight 2 ≤ 1)
    (hw3 : 6 * point.weight 3 ≤ 1) (hw5 : 6 * point.weight 5 ≤ 1) :
    KFourUnsignedStarBCellFires point := by
  have hw0pos := point.weight_pos 0
  have hw2pos := point.weight_pos 2
  have hw3pos := point.weight_pos 3
  have hw5pos := point.weight_pos 5
  have hm3pos := point.mass_pos 3
  have hm5pos := point.mass_pos 5
  have hcap3 : 5 * point.mass 3 ≤ s * (z 0 * (z 0 + z 1 + z 2)) := by
    have hstep : (5 * point.mass 3) * point.weight 3
        ≤ (s * (z 0 * (z 0 + z 1 + z 2))) * point.weight 3 := by
      nlinarith [hd3, hm3pos]
    exact le_of_mul_le_mul_right hstep hw3pos
  have hcap5 : 5 * point.mass 5 ≤ s * (z 2 * (z 0 + z 1 + z 2)) := by
    have hstep : (5 * point.mass 5) * point.weight 5
        ≤ (s * (z 2 * (z 0 + z 1 + z 2))) * point.weight 5 := by
      nlinarith [hd5, hm5pos]
    exact le_of_mul_le_mul_right hstep hw5pos
  refine ⟨5 * (s * (z 0 * z 1)), 5 * (s * (z 1 * z 2)),
    s * (z 1 * (z 0 + z 1 + z 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm0]
    nlinarith [mul_pos hs (mul_pos hz0 hz1)]
  · rw [hm2]
    nlinarith [mul_pos hs (mul_pos hz1 hz2)]
  · rw [hd4]
  · rw [hm1]
    nlinarith [hcap3, mul_pos (mul_pos hs hz0) hz1,
      mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz0).le,
      mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz0).le]
  · rw [hm1]
    have hA : 17 / 5 * (s * (z 0 * z 1))
        ≤ 5 * (s * (z 0 * z 1)) - (s * (z 0 * z 2) + point.mass 3) := by
      nlinarith [hcap3, mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz0).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz0).le]
    have hB : 17 / 5 * (s * (z 1 * z 2))
        ≤ 5 * (s * (z 1 * z 2)) - (s * (z 0 * z 2) + point.mass 5) := by
      nlinarith [hcap5, mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz2).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz2).le]
    have hApos : 0 < 17 / 5 * (s * (z 0 * z 1)) := by positivity
    have hBpos : 0 < 17 / 5 * (s * (z 1 * z 2)) := by positivity
    have hprod : (17 / 5 * (s * (z 0 * z 1))) * (17 / 5 * (s * (z 1 * z 2)))
        ≤ (5 * (s * (z 0 * z 1)) - (s * (z 0 * z 2) + point.mass 3))
          * (5 * (s * (z 1 * z 2)) - (s * (z 0 * z 2) + point.mass 5)) :=
      mul_le_mul hA hB hBpos.le (le_trans hApos.le hA)
    nlinarith [hprod, mul_le_mul hmax0 hmax2 hz2.le hz1.le,
      mul_pos (mul_pos hs hs) (mul_pos hz0 hz2),
      mul_pos (mul_pos (mul_pos hs hs) (mul_pos hz0 hz2)) (mul_pos hz1 hz1)]
  · rw [hm1]
    set sg := z 0 + z 1 + z 2 with hsg
    have hsgpos : 0 < sg := by rw [hsg]; linarith
    have hsgle : sg ≤ 3 * z 1 := by rw [hsg]; linarith
    have hA : 17 / 5 * (s * (z 0 * z 1))
        ≤ 5 * (s * (z 0 * z 1)) - (s * (z 0 * z 2) + point.mass 3) := by
      nlinarith [hcap3, mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz0).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz0).le]
    have hB : 17 / 5 * (s * (z 1 * z 2))
        ≤ 5 * (s * (z 1 * z 2)) - (s * (z 0 * z 2) + point.mass 5) := by
      nlinarith [hcap5, mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz2).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz2).le]
    have hC : 3 / 5 * (s * (z 1 * sg))
        ≤ s * (z 1 * sg) - (point.mass 3 + point.mass 5) := by
      nlinarith [hcap3, hcap5,
        mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hsgpos).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hsgpos).le,
        mul_pos hs (mul_pos hz1 hsgpos)]
    have hAup : 5 * (s * (z 0 * z 1)) - (s * (z 0 * z 2) + point.mass 3)
        ≤ 5 * (s * (z 0 * z 1)) := by
      nlinarith [mul_pos hs (mul_pos hz0 hz2), hm3pos]
    have hBup : 5 * (s * (z 1 * z 2)) - (s * (z 0 * z 2) + point.mass 5)
        ≤ 5 * (s * (z 1 * z 2)) := by
      nlinarith [mul_pos hs (mul_pos hz0 hz2), hm5pos]
    have hCup : s * (z 1 * sg) - (point.mass 3 + point.mass 5)
        ≤ s * (z 1 * sg) := by nlinarith [hm3pos, hm5pos]
    have hApos : 0 < 17 / 5 * (s * (z 0 * z 1)) := by positivity
    have hBpos : 0 < 17 / 5 * (s * (z 1 * z 2)) := by positivity
    have hCpos : 0 < 3 / 5 * (s * (z 1 * sg)) := by positivity
    set aa := 5 * (s * (z 0 * z 1)) - (s * (z 0 * z 2) + point.mass 3) with haa
    set bb := 5 * (s * (z 1 * z 2)) - (s * (z 0 * z 2) + point.mass 5) with hbb
    set cc := s * (z 1 * sg) - (point.mass 3 + point.mass 5) with hcc
    have haapos : 0 < aa := lt_of_lt_of_le hApos hA
    have hbbpos : 0 < bb := lt_of_lt_of_le hBpos hB
    have hccpos : 0 < cc := lt_of_lt_of_le hCpos hC
    have habc : (17 / 5 * (s * (z 0 * z 1))) * (17 / 5 * (s * (z 1 * z 2)))
        * (3 / 5 * (s * (z 1 * sg))) ≤ aa * bb * cc := by
      have h1 : (17 / 5 * (s * (z 0 * z 1))) * (17 / 5 * (s * (z 1 * z 2)))
          ≤ aa * bb := mul_le_mul hA hB hBpos.le haapos.le
      exact mul_le_mul h1 hC hCpos.le (mul_nonneg haapos.le hbbpos.le)
    have hR2 : point.mass 5 ^ 2 ≤ (s * (z 2 * sg) / 5) ^ 2 := by
      have h5 : point.mass 5 ≤ s * (z 2 * sg) / 5 := by linarith
      nlinarith [mul_self_le_mul_self hm5pos.le h5]
    have hQ2 : point.mass 3 ^ 2 ≤ (s * (z 0 * sg) / 5) ^ 2 := by
      have h3 : point.mass 3 ≤ s * (z 0 * sg) / 5 := by linarith
      nlinarith [mul_self_le_mul_self hm3pos.le h3]
    have haR2 : aa * point.mass 5 ^ 2
        ≤ 5 * (s * (z 0 * z 1)) * ((s * (z 2 * sg) / 5) ^ 2) := by
      have := mul_le_mul hAup hR2 (sq_nonneg (point.mass 5)) (by positivity)
      linarith
    have hbQ2 : point.mass 3 ^ 2 * bb
        ≤ (s * (z 0 * sg) / 5) ^ 2 * (5 * (s * (z 1 * z 2))) := by
      have := mul_le_mul hQ2 hBup hbbpos.le (by positivity)
      linarith
    have hcP2 : (s * (z 0 * z 2)) ^ 2 * cc
        ≤ (s * (z 0 * z 2)) ^ 2 * (s * (z 1 * sg)) := by
      have := mul_le_mul_of_nonneg_left hCup (sq_nonneg (s * (z 0 * z 2)))
      linarith
    have hPQR : 2 * (s * (z 0 * z 2)) * point.mass 3 * point.mass 5
        ≤ 2 * (s * (z 0 * z 2)) * (s * (z 0 * sg) / 5) * (s * (z 2 * sg) / 5) := by
      have h3 : point.mass 3 ≤ s * (z 0 * sg) / 5 := by linarith
      have h5 : point.mass 5 ≤ s * (z 2 * sg) / 5 := by linarith
      have hP2 : 0 < 2 * (s * (z 0 * z 2)) := by positivity
      have hstep : 2 * (s * (z 0 * z 2)) * point.mass 3
          ≤ 2 * (s * (z 0 * z 2)) * (s * (z 0 * sg) / 5) :=
        mul_le_mul_of_nonneg_left h3 hP2.le
      calc 2 * (s * (z 0 * z 2)) * point.mass 3 * point.mass 5
          ≤ 2 * (s * (z 0 * z 2)) * (s * (z 0 * sg) / 5) * point.mass 5 :=
            mul_le_mul_of_nonneg_right hstep hm5pos.le
        _ ≤ 2 * (s * (z 0 * z 2)) * (s * (z 0 * sg) / 5)
              * (s * (z 2 * sg) / 5) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
    have hXpos : 0 < s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))
        := by positivity
    have hz2sg : z 2 * sg ≤ 3 * (z 1 * z 1) := by nlinarith [hmax2, hsgle]
    have hz0sg : z 0 * sg ≤ 3 * (z 1 * z 1) := by nlinarith [hmax0, hsgle]
    have hz02 : z 0 * z 2 ≤ z 1 * z 1 :=
      mul_le_mul hmax0 hmax2 hz2.le hz1.le
    have hT1 : 5 * (s * (z 0 * z 1)) * ((s * (z 2 * sg) / 5) ^ 2)
        ≤ 3 / 5 * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz2sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz1.le hz0.le)
            (mul_nonneg hz2.le hsgpos.le)))]
    have hT2 : (s * (z 0 * sg) / 5) ^ 2 * (5 * (s * (z 1 * z 2)))
        ≤ 3 / 5 * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz0sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz1.le hz2.le)
            (mul_nonneg hz0.le hsgpos.le)))]
    have hT3 : (s * (z 0 * z 2)) ^ 2 * (s * (z 1 * sg))
        ≤ 1 * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz02
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz1.le hsgpos.le)
            (mul_nonneg hz0.le hz2.le)))]
    have hT4 : 2 * (s * (z 0 * z 2)) * (s * (z 0 * sg) / 5) * (s * (z 2 * sg) / 5)
        ≤ 6 / 25 * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))) := by
      have hz02sg : z 0 * z 2 * sg ≤ z 1 * z 1 * (3 * z 1) := by
        nlinarith [mul_le_mul_of_nonneg_left hsgle (mul_nonneg hz0.le hz2.le),
          mul_le_mul_of_nonneg_right hz02 hsgpos.le]
      nlinarith [mul_le_mul_of_nonneg_left hz02sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz0.le hz2.le) hsgpos.le))]
    have hRHS : (17 / 5 * (s * (z 0 * z 1))) * (17 / 5 * (s * (z 1 * z 2)))
          * (3 / 5 * (s * (z 1 * sg)))
        = 867 / 125 * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))) := by
      ring
    have hMain : 867 / 125
          * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg))))
        ≤ aa * bb * cc := hRHS ▸ habc
    have hN1 : aa * point.mass 5 ^ 2
        ≤ 3 / 5 * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))) :=
      le_trans haR2 hT1
    have hN2 : point.mass 3 ^ 2 * bb
        ≤ 3 / 5 * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))) :=
      le_trans hbQ2 hT2
    have hN3 : (s * (z 0 * z 2)) ^ 2 * cc
        ≤ 1 * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))) :=
      le_trans hcP2 hT3
    have hN4 : 2 * (s * (z 0 * z 2)) * point.mass 3 * point.mass 5
        ≤ 6 / 25 * (s * s * s * (z 1 * z 1 * z 1 * (z 0 * (z 2 * sg)))) :=
      le_trans hPQR hT4
    linarith [hMain, hN1, hN2, hN3, hN4, hXpos]

/-! ## 2. The vertex-c mirror -/

/-- **The balanced case at the vertex-c star.**  Third axis coordinate
maximal, the star's four weights at most one sixth. -/
theorem kFourStarCCell_fires_of_wall_balanced (point : DirectionChartPoint 6)
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
    (hmax0 : z 0 ≤ z 2) (hmax1 : z 1 ≤ z 2)
    (hw1 : 6 * point.weight 1 ≤ 1) (hw2 : 6 * point.weight 2 ≤ 1)
    (hw3 : 6 * point.weight 3 ≤ 1) (hw4 : 6 * point.weight 4 ≤ 1) :
    KFourUnsignedStarCCellFires point := by
  have hw1pos := point.weight_pos 1
  have hw2pos := point.weight_pos 2
  have hw3pos := point.weight_pos 3
  have hw4pos := point.weight_pos 4
  have hm3pos := point.mass_pos 3
  have hm4pos := point.mass_pos 4
  have hcap3 : 5 * point.mass 3 ≤ s * (z 0 * (z 0 + z 1 + z 2)) := by
    have hstep : (5 * point.mass 3) * point.weight 3
        ≤ (s * (z 0 * (z 0 + z 1 + z 2))) * point.weight 3 := by
      nlinarith [hd3, hm3pos]
    exact le_of_mul_le_mul_right hstep hw3pos
  have hcap4 : 5 * point.mass 4 ≤ s * (z 1 * (z 0 + z 1 + z 2)) := by
    have hstep : (5 * point.mass 4) * point.weight 4
        ≤ (s * (z 1 * (z 0 + z 1 + z 2))) * point.weight 4 := by
      nlinarith [hd4, hm4pos]
    exact le_of_mul_le_mul_right hstep hw4pos
  refine ⟨5 * (s * (z 0 * z 2)), 5 * (s * (z 1 * z 2)),
    s * (z 2 * (z 0 + z 1 + z 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm1]
    nlinarith [mul_pos hs (mul_pos hz0 hz2)]
  · rw [hm2]
    nlinarith [mul_pos hs (mul_pos hz1 hz2)]
  · rw [hd5]
  · rw [hm0]
    nlinarith [hcap3, mul_pos (mul_pos hs hz0) hz2,
      mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz0).le,
      mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz0).le]
  · rw [hm0]
    have hA : 17 / 5 * (s * (z 0 * z 2))
        ≤ 5 * (s * (z 0 * z 2)) - (s * (z 0 * z 1) + point.mass 3) := by
      nlinarith [hcap3, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz0).le,
        mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz0).le]
    have hB : 17 / 5 * (s * (z 1 * z 2))
        ≤ 5 * (s * (z 1 * z 2)) - (s * (z 0 * z 1) + point.mass 4) := by
      nlinarith [hcap4, mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz1).le,
        mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz1).le]
    have hApos : 0 < 17 / 5 * (s * (z 0 * z 2)) := by positivity
    have hBpos : 0 < 17 / 5 * (s * (z 1 * z 2)) := by positivity
    have hprod : (17 / 5 * (s * (z 0 * z 2))) * (17 / 5 * (s * (z 1 * z 2)))
        ≤ (5 * (s * (z 0 * z 2)) - (s * (z 0 * z 1) + point.mass 3))
          * (5 * (s * (z 1 * z 2)) - (s * (z 0 * z 1) + point.mass 4)) :=
      mul_le_mul hA hB hBpos.le (le_trans hApos.le hA)
    nlinarith [hprod, mul_le_mul hmax0 hmax1 hz1.le hz2.le,
      mul_pos (mul_pos hs hs) (mul_pos hz0 hz1),
      mul_pos (mul_pos (mul_pos hs hs) (mul_pos hz0 hz1)) (mul_pos hz2 hz2)]
  · rw [hm0]
    set sg := z 0 + z 1 + z 2 with hsg
    have hsgpos : 0 < sg := by rw [hsg]; linarith
    have hsgle : sg ≤ 3 * z 2 := by rw [hsg]; linarith
    have hA : 17 / 5 * (s * (z 0 * z 2))
        ≤ 5 * (s * (z 0 * z 2)) - (s * (z 0 * z 1) + point.mass 3) := by
      nlinarith [hcap3, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz0).le,
        mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz0).le]
    have hB : 17 / 5 * (s * (z 1 * z 2))
        ≤ 5 * (s * (z 1 * z 2)) - (s * (z 0 * z 1) + point.mass 4) := by
      nlinarith [hcap4, mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hz1).le,
        mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz1).le]
    have hC : 3 / 5 * (s * (z 2 * sg))
        ≤ s * (z 2 * sg) - (point.mass 3 + point.mass 4) := by
      nlinarith [hcap3, hcap4,
        mul_le_mul_of_nonneg_left hmax0 (mul_pos hs hsgpos).le,
        mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hsgpos).le,
        mul_pos hs (mul_pos hz2 hsgpos)]
    have hAup : 5 * (s * (z 0 * z 2)) - (s * (z 0 * z 1) + point.mass 3)
        ≤ 5 * (s * (z 0 * z 2)) := by
      nlinarith [mul_pos hs (mul_pos hz0 hz1), hm3pos]
    have hBup : 5 * (s * (z 1 * z 2)) - (s * (z 0 * z 1) + point.mass 4)
        ≤ 5 * (s * (z 1 * z 2)) := by
      nlinarith [mul_pos hs (mul_pos hz0 hz1), hm4pos]
    have hCup : s * (z 2 * sg) - (point.mass 3 + point.mass 4)
        ≤ s * (z 2 * sg) := by nlinarith [hm3pos, hm4pos]
    have hApos : 0 < 17 / 5 * (s * (z 0 * z 2)) := by positivity
    have hBpos : 0 < 17 / 5 * (s * (z 1 * z 2)) := by positivity
    have hCpos : 0 < 3 / 5 * (s * (z 2 * sg)) := by positivity
    set aa := 5 * (s * (z 0 * z 2)) - (s * (z 0 * z 1) + point.mass 3) with haa
    set bb := 5 * (s * (z 1 * z 2)) - (s * (z 0 * z 1) + point.mass 4) with hbb
    set cc := s * (z 2 * sg) - (point.mass 3 + point.mass 4) with hcc
    have haapos : 0 < aa := lt_of_lt_of_le hApos hA
    have hbbpos : 0 < bb := lt_of_lt_of_le hBpos hB
    have hccpos : 0 < cc := lt_of_lt_of_le hCpos hC
    have habc : (17 / 5 * (s * (z 0 * z 2))) * (17 / 5 * (s * (z 1 * z 2)))
        * (3 / 5 * (s * (z 2 * sg))) ≤ aa * bb * cc := by
      have h1 : (17 / 5 * (s * (z 0 * z 2))) * (17 / 5 * (s * (z 1 * z 2)))
          ≤ aa * bb := mul_le_mul hA hB hBpos.le haapos.le
      exact mul_le_mul h1 hC hCpos.le (mul_nonneg haapos.le hbbpos.le)
    have hR2 : point.mass 4 ^ 2 ≤ (s * (z 1 * sg) / 5) ^ 2 := by
      have h4 : point.mass 4 ≤ s * (z 1 * sg) / 5 := by linarith
      nlinarith [mul_self_le_mul_self hm4pos.le h4]
    have hQ2 : point.mass 3 ^ 2 ≤ (s * (z 0 * sg) / 5) ^ 2 := by
      have h3 : point.mass 3 ≤ s * (z 0 * sg) / 5 := by linarith
      nlinarith [mul_self_le_mul_self hm3pos.le h3]
    have haR2 : aa * point.mass 4 ^ 2
        ≤ 5 * (s * (z 0 * z 2)) * ((s * (z 1 * sg) / 5) ^ 2) := by
      have := mul_le_mul hAup hR2 (sq_nonneg (point.mass 4)) (by positivity)
      linarith
    have hbQ2 : point.mass 3 ^ 2 * bb
        ≤ (s * (z 0 * sg) / 5) ^ 2 * (5 * (s * (z 1 * z 2))) := by
      have := mul_le_mul hQ2 hBup hbbpos.le (by positivity)
      linarith
    have hcP2 : (s * (z 0 * z 1)) ^ 2 * cc
        ≤ (s * (z 0 * z 1)) ^ 2 * (s * (z 2 * sg)) := by
      have := mul_le_mul_of_nonneg_left hCup (sq_nonneg (s * (z 0 * z 1)))
      linarith
    have hPQR : 2 * (s * (z 0 * z 1)) * point.mass 3 * point.mass 4
        ≤ 2 * (s * (z 0 * z 1)) * (s * (z 0 * sg) / 5) * (s * (z 1 * sg) / 5) := by
      have h3 : point.mass 3 ≤ s * (z 0 * sg) / 5 := by linarith
      have h4 : point.mass 4 ≤ s * (z 1 * sg) / 5 := by linarith
      have hP2 : 0 < 2 * (s * (z 0 * z 1)) := by positivity
      have hstep : 2 * (s * (z 0 * z 1)) * point.mass 3
          ≤ 2 * (s * (z 0 * z 1)) * (s * (z 0 * sg) / 5) :=
        mul_le_mul_of_nonneg_left h3 hP2.le
      calc 2 * (s * (z 0 * z 1)) * point.mass 3 * point.mass 4
          ≤ 2 * (s * (z 0 * z 1)) * (s * (z 0 * sg) / 5) * point.mass 4 :=
            mul_le_mul_of_nonneg_right hstep hm4pos.le
        _ ≤ 2 * (s * (z 0 * z 1)) * (s * (z 0 * sg) / 5)
              * (s * (z 1 * sg) / 5) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
    have hXpos : 0 < s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))
        := by positivity
    have hz1sg : z 1 * sg ≤ 3 * (z 2 * z 2) := by nlinarith [hmax1, hsgle]
    have hz0sg : z 0 * sg ≤ 3 * (z 2 * z 2) := by nlinarith [hmax0, hsgle]
    have hz01 : z 0 * z 1 ≤ z 2 * z 2 :=
      mul_le_mul hmax0 hmax1 hz1.le hz2.le
    have hT1 : 5 * (s * (z 0 * z 2)) * ((s * (z 1 * sg) / 5) ^ 2)
        ≤ 3 / 5 * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz1sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz2.le hz0.le)
            (mul_nonneg hz1.le hsgpos.le)))]
    have hT2 : (s * (z 0 * sg) / 5) ^ 2 * (5 * (s * (z 1 * z 2)))
        ≤ 3 / 5 * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz0sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz2.le hz1.le)
            (mul_nonneg hz0.le hsgpos.le)))]
    have hT3 : (s * (z 0 * z 1)) ^ 2 * (s * (z 2 * sg))
        ≤ 1 * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz01
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz2.le hsgpos.le)
            (mul_nonneg hz0.le hz1.le)))]
    have hT4 : 2 * (s * (z 0 * z 1)) * (s * (z 0 * sg) / 5) * (s * (z 1 * sg) / 5)
        ≤ 6 / 25 * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))) := by
      have hz01sg : z 0 * z 1 * sg ≤ z 2 * z 2 * (3 * z 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hsgle (mul_nonneg hz0.le hz1.le),
          mul_le_mul_of_nonneg_right hz01 hsgpos.le]
      nlinarith [mul_le_mul_of_nonneg_left hz01sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz0.le hz1.le) hsgpos.le))]
    have hRHS : (17 / 5 * (s * (z 0 * z 2))) * (17 / 5 * (s * (z 1 * z 2)))
          * (3 / 5 * (s * (z 2 * sg)))
        = 867 / 125 * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))) := by
      ring
    have hMain : 867 / 125
          * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg))))
        ≤ aa * bb * cc := hRHS ▸ habc
    have hN1 : aa * point.mass 4 ^ 2
        ≤ 3 / 5 * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))) :=
      le_trans haR2 hT1
    have hN2 : point.mass 3 ^ 2 * bb
        ≤ 3 / 5 * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))) :=
      le_trans hbQ2 hT2
    have hN3 : (s * (z 0 * z 1)) ^ 2 * cc
        ≤ 1 * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))) :=
      le_trans hcP2 hT3
    have hN4 : 2 * (s * (z 0 * z 1)) * point.mass 3 * point.mass 4
        ≤ 6 / 25 * (s * s * s * (z 2 * z 2 * z 2 * (z 0 * (z 1 * sg)))) :=
      le_trans hPQR hT4
    linarith [hMain, hN1, hN2, hN3, hN4, hXpos]

/-! ## 3. The assemblies -/

/-- The vertex-b balanced case fires the full minor atlas. -/
theorem kFourAtlas_fires_of_wall_balancedB (point : DirectionChartPoint 6)
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
    (hmax0 : z 0 ≤ z 1) (hmax2 : z 2 ≤ z 1)
    (hw0 : 6 * point.weight 0 ≤ 1) (hw2 : 6 * point.weight 2 ≤ 1)
    (hw3 : 6 * point.weight 3 ≤ 1) (hw5 : 6 * point.weight 5 ≤ 1) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
    (kFourStarBCell_fires_of_wall_balanced point hz0 hz1 hz2 hs hm0 hm1 hm2
      hd3 hd4 hd5 hmax0 hmax2 hw0 hw2 hw3 hw5))))))

/-- The vertex-c balanced case fires the full minor atlas. -/
theorem kFourAtlas_fires_of_wall_balancedC (point : DirectionChartPoint 6)
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
    (hmax0 : z 0 ≤ z 2) (hmax1 : z 1 ≤ z 2)
    (hw1 : 6 * point.weight 1 ≤ 1) (hw2 : 6 * point.weight 2 ≤ 1)
    (hw3 : 6 * point.weight 3 ≤ 1) (hw4 : 6 * point.weight 4 ≤ 1) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
    (kFourStarCCell_fires_of_wall_balanced point hz0 hz1 hz2 hs hm0 hm1 hm2
      hd3 hd4 hd5 hmax0 hmax1 hw1 hw2 hw3 hw4))))))

end Gtz
