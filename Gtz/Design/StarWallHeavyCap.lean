import Gtz.Design.StarWallVacuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The heavy weight cap of the gauge star wall

The landed balanced case of the gauge star wall asks every sensitive weight to
be at most `1/6`.  That bound is not sharp.  This module raises the cap to
`3/16` with the same term-bound architecture.

* `kFourStarACell_fires_of_wall_heavyCap` is the vertex-a cell at the wider
  cap.  The witness floors are `13/3` times the two triangle masses and the
  exact third boost, and the demand caps read `13 m ≤ 3 b`.
* `kFourAtlas_fires_of_wall_heavyCap` fires the full minor atlas there.

The cap `3/16` is inside the exact wall threshold `(3 - √3)/6`, which is where
the vertex-a cell itself stops firing at the symmetric axis.  The term-bound
architecture stalls before that threshold: it needs the boost quotient at least
about `4.08`, and the threshold is `2 + √3`.
-/

namespace Gtz

open Matrix Finset

/-- **THE HEAVY CAP OF THE VERTEX-A CELL.**  On the gauge star wall with the
maximal axis at slot zero, a sensitive weight cap of `3/16` still fires the
vertex-a cell.  The two triangle floors are `13/3` times their masses, and the
third floor is the exact boost. -/
theorem kFourStarACell_fires_of_wall_heavyCap (point : DirectionChartPoint 6)
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
    (hw0 : 16 * point.weight 0 ≤ 3) (hw1 : 16 * point.weight 1 ≤ 3)
    (hw4 : 16 * point.weight 4 ≤ 3) (hw5 : 16 * point.weight 5 ≤ 3) :
    KFourUnsignedStarACellFires point := by
  have hw0pos := point.weight_pos 0
  have hw1pos := point.weight_pos 1
  have hw4pos := point.weight_pos 4
  have hw5pos := point.weight_pos 5
  have hm4pos := point.mass_pos 4
  have hm5pos := point.mass_pos 5
  -- the two demand caps at the wider weight cap
  have hcap4 : 13 * point.mass 4 ≤ 3 * (s * (z 1 * (z 0 + z 1 + z 2))) := by
    have hstep : (13 * point.mass 4) * point.weight 4
        ≤ (3 * (s * (z 1 * (z 0 + z 1 + z 2)))) * point.weight 4 := by
      nlinarith [hd4, hm4pos]
    exact le_of_mul_le_mul_right hstep hw4pos
  have hcap5 : 13 * point.mass 5 ≤ 3 * (s * (z 2 * (z 0 + z 1 + z 2))) := by
    have hstep : (13 * point.mass 5) * point.weight 5
        ≤ (3 * (s * (z 2 * (z 0 + z 1 + z 2)))) * point.weight 5 := by
      nlinarith [hd5, hm5pos]
    exact le_of_mul_le_mul_right hstep hw5pos
  refine ⟨13 / 3 * (s * (z 0 * z 1)), 13 / 3 * (s * (z 0 * z 2)),
    s * (z 0 * (z 0 + z 1 + z 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm0]
    nlinarith [mul_pos hs (mul_pos hz0 hz1)]
  · rw [hm1]
    nlinarith [mul_pos hs (mul_pos hz0 hz2)]
  · rw [hd3]
  · -- the corner
    rw [hm2]
    nlinarith [hcap4, mul_pos (mul_pos hs hz1) hz0,
      mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz1).le,
      mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz1).le]
  · -- the second minor
    rw [hm2]
    have hA : 5 / 2 * (s * (z 0 * z 1))
        ≤ 13 / 3 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4) := by
      nlinarith [hcap4, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz1).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz1).le]
    have hB : 5 / 2 * (s * (z 0 * z 2))
        ≤ 13 / 3 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5) := by
      nlinarith [hcap5, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz2).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz2).le]
    have hApos : 0 < 5 / 2 * (s * (z 0 * z 1)) := by positivity
    have hBpos : 0 < 5 / 2 * (s * (z 0 * z 2)) := by positivity
    have hprod : (5 / 2 * (s * (z 0 * z 1))) * (5 / 2 * (s * (z 0 * z 2)))
        ≤ (13 / 3 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4))
          * (13 / 3 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5)) :=
      mul_le_mul hA hB hBpos.le (le_trans hApos.le hA)
    nlinarith [hprod, mul_le_mul hmax1 hmax2 hz2.le hz0.le,
      mul_pos (mul_pos hs hs) (mul_pos hz1 hz2),
      mul_pos (mul_pos (mul_pos hs hs) (mul_pos hz1 hz2)) (mul_pos hz0 hz0)]
  · -- the determinant
    rw [hm2]
    set sg := z 0 + z 1 + z 2 with hsg
    have hsgpos : 0 < sg := by rw [hsg]; linarith
    have hsgle : sg ≤ 3 * z 0 := by rw [hsg]; linarith
    have hA : 5 / 2 * (s * (z 0 * z 1))
        ≤ 13 / 3 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4) := by
      nlinarith [hcap4, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz1).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz1).le]
    have hB : 5 / 2 * (s * (z 0 * z 2))
        ≤ 13 / 3 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5) := by
      nlinarith [hcap5, mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hz2).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hz2).le]
    have hC : 1 / 2 * (s * (z 0 * sg))
        ≤ s * (z 0 * sg) - (point.mass 4 + point.mass 5) := by
      nlinarith [hcap4, hcap5,
        mul_le_mul_of_nonneg_left hmax1 (mul_pos hs hsgpos).le,
        mul_le_mul_of_nonneg_left hmax2 (mul_pos hs hsgpos).le,
        mul_pos hs (mul_pos hz0 hsgpos)]
    have hAup : 13 / 3 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4)
        ≤ 13 / 3 * (s * (z 0 * z 1)) := by
      nlinarith [mul_pos hs (mul_pos hz1 hz2), hm4pos]
    have hBup : 13 / 3 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5)
        ≤ 13 / 3 * (s * (z 0 * z 2)) := by
      nlinarith [mul_pos hs (mul_pos hz1 hz2), hm5pos]
    have hCup : s * (z 0 * sg) - (point.mass 4 + point.mass 5)
        ≤ s * (z 0 * sg) := by nlinarith [hm4pos, hm5pos]
    have hApos : 0 < 5 / 2 * (s * (z 0 * z 1)) := by positivity
    have hBpos : 0 < 5 / 2 * (s * (z 0 * z 2)) := by positivity
    have hCpos : 0 < 1 / 2 * (s * (z 0 * sg)) := by positivity
    set aa := 13 / 3 * (s * (z 0 * z 1)) - (s * (z 1 * z 2) + point.mass 4) with haa
    set bb := 13 / 3 * (s * (z 0 * z 2)) - (s * (z 1 * z 2) + point.mass 5) with hbb
    set cc := s * (z 0 * sg) - (point.mass 4 + point.mass 5) with hcc
    have haapos : 0 < aa := lt_of_lt_of_le hApos hA
    have hbbpos : 0 < bb := lt_of_lt_of_le hBpos hB
    have hccpos : 0 < cc := lt_of_lt_of_le hCpos hC
    have habc : (5 / 2 * (s * (z 0 * z 1))) * (5 / 2 * (s * (z 0 * z 2)))
        * (1 / 2 * (s * (z 0 * sg))) ≤ aa * bb * cc := by
      have h1 : (5 / 2 * (s * (z 0 * z 1))) * (5 / 2 * (s * (z 0 * z 2)))
          ≤ aa * bb := mul_le_mul hA hB hBpos.le haapos.le
      exact mul_le_mul h1 hC hCpos.le (mul_nonneg haapos.le hbbpos.le)
    have hR2 : point.mass 5 ^ 2 ≤ (3 * (s * (z 2 * sg)) / 13) ^ 2 := by
      have h5 : point.mass 5 ≤ 3 * (s * (z 2 * sg)) / 13 := by
        linarith [hcap5]
      nlinarith [mul_self_le_mul_self hm5pos.le h5]
    have hQ2 : point.mass 4 ^ 2 ≤ (3 * (s * (z 1 * sg)) / 13) ^ 2 := by
      have h4 : point.mass 4 ≤ 3 * (s * (z 1 * sg)) / 13 := by
        linarith [hcap4]
      nlinarith [mul_self_le_mul_self hm4pos.le h4]
    have haR2 : aa * point.mass 5 ^ 2
        ≤ 13 / 3 * (s * (z 0 * z 1)) * ((3 * (s * (z 2 * sg)) / 13) ^ 2) := by
      have := mul_le_mul hAup hR2 (sq_nonneg (point.mass 5)) (by positivity)
      linarith
    have hbQ2 : point.mass 4 ^ 2 * bb
        ≤ (3 * (s * (z 1 * sg)) / 13) ^ 2 * (13 / 3 * (s * (z 0 * z 2))) := by
      have := mul_le_mul hQ2 hBup hbbpos.le (by positivity)
      linarith
    have hcP2 : (s * (z 1 * z 2)) ^ 2 * cc
        ≤ (s * (z 1 * z 2)) ^ 2 * (s * (z 0 * sg)) := by
      have := mul_le_mul_of_nonneg_left hCup (sq_nonneg (s * (z 1 * z 2)))
      linarith
    have hPQR : 2 * (s * (z 1 * z 2)) * point.mass 4 * point.mass 5
        ≤ 2 * (s * (z 1 * z 2)) * (3 * (s * (z 1 * sg)) / 13)
            * (3 * (s * (z 2 * sg)) / 13) := by
      have h4 : point.mass 4 ≤ 3 * (s * (z 1 * sg)) / 13 := by
        linarith [hcap4]
      have h5 : point.mass 5 ≤ 3 * (s * (z 2 * sg)) / 13 := by
        linarith [hcap5]
      have hP2 : 0 < 2 * (s * (z 1 * z 2)) := by positivity
      have hstep : 2 * (s * (z 1 * z 2)) * point.mass 4
          ≤ 2 * (s * (z 1 * z 2)) * (3 * (s * (z 1 * sg)) / 13) :=
        mul_le_mul_of_nonneg_left h4 hP2.le
      calc 2 * (s * (z 1 * z 2)) * point.mass 4 * point.mass 5
          ≤ 2 * (s * (z 1 * z 2)) * (3 * (s * (z 1 * sg)) / 13) * point.mass 5 :=
            mul_le_mul_of_nonneg_right hstep hm5pos.le
        _ ≤ 2 * (s * (z 1 * z 2)) * (3 * (s * (z 1 * sg)) / 13)
              * (3 * (s * (z 2 * sg)) / 13) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
    have hXpos : 0 < s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))
        := by positivity
    have hz2sg : z 2 * sg ≤ 3 * (z 0 * z 0) := by nlinarith [hmax2, hsgle]
    have hz1sg : z 1 * sg ≤ 3 * (z 0 * z 0) := by nlinarith [hmax1, hsgle]
    have hz12 : z 1 * z 2 ≤ z 0 * z 0 :=
      mul_le_mul hmax1 hmax2 hz2.le hz0.le
    have hT1 : 13 / 3 * (s * (z 0 * z 1)) * ((3 * (s * (z 2 * sg)) / 13) ^ 2)
        ≤ 7 / 10 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
      nlinarith [mul_le_mul_of_nonneg_left hz2sg
        (mul_nonneg (mul_nonneg (mul_nonneg hs.le hs.le) hs.le)
          (mul_nonneg (mul_nonneg hz0.le hz1.le)
            (mul_nonneg hz2.le hsgpos.le)))]
    have hT2 : (3 * (s * (z 1 * sg)) / 13) ^ 2 * (13 / 3 * (s * (z 0 * z 2)))
        ≤ 7 / 10 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
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
    have hT4 : 2 * (s * (z 1 * z 2)) * (3 * (s * (z 1 * sg)) / 13)
          * (3 * (s * (z 2 * sg)) / 13)
        ≤ 1 / 3 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
      have hz12sg : z 1 * z 2 * sg ≤ z 0 * z 0 * (3 * z 0) :=
        mul_le_mul hz12 hsgle hsgpos.le (by positivity)
      have hsq : (z 1 * z 2 * sg) * (z 1 * z 2 * sg)
          ≤ (z 0 * z 0 * (3 * z 0)) * (z 1 * z 2 * sg) :=
        mul_le_mul_of_nonneg_right hz12sg (by positivity)
      have key : s * s * s * ((z 1 * z 2 * sg) * (z 1 * z 2 * sg))
          ≤ s * s * s * ((z 0 * z 0 * (3 * z 0)) * (z 1 * z 2 * sg)) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      have e1 : 2 * (s * (z 1 * z 2)) * (3 * (s * (z 1 * sg)) / 13)
            * (3 * (s * (z 2 * sg)) / 13)
          = 18 / 169 * (s * s * s * ((z 1 * z 2 * sg) * (z 1 * z 2 * sg))) := by
        ring
      have e2 : (18 : ℝ) / 169 * (s * s * s * ((z 0 * z 0 * (3 * z 0))
            * (z 1 * z 2 * sg)))
          = 54 / 169 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
        ring
      have estep : 18 / 169 * (s * s * s * ((z 1 * z 2 * sg) * (z 1 * z 2 * sg)))
          ≤ 18 / 169 * (s * s * s * ((z 0 * z 0 * (3 * z 0)) * (z 1 * z 2 * sg))) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
      linarith [hXpos, e1, e2, estep]
    have hRHS : (5 / 2 * (s * (z 0 * z 1))) * (5 / 2 * (s * (z 0 * z 2)))
          * (1 / 2 * (s * (z 0 * sg)))
        = 25 / 8 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) := by
      ring
    have hMain : 25 / 8
          * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg))))
        ≤ aa * bb * cc := le_trans (le_of_eq hRHS.symm) habc
    have hN1 : aa * point.mass 5 ^ 2
        ≤ 7 / 10 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) :=
      le_trans haR2 hT1
    have hN2 : point.mass 4 ^ 2 * bb
        ≤ 7 / 10 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) :=
      le_trans hbQ2 hT2
    have hN3 : (s * (z 1 * z 2)) ^ 2 * cc
        ≤ 1 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) :=
      le_trans hcP2 hT3
    have hN4 : 2 * (s * (z 1 * z 2)) * point.mass 4 * point.mass 5
        ≤ 1 / 3 * (s * s * s * (z 0 * z 0 * z 0 * (z 1 * (z 2 * sg)))) :=
      le_trans hPQR hT4
    linarith [hMain, hN1, hN2, hN3, hN4, hXpos]

/-- The heavy-cap wall case fires the full minor atlas. -/
theorem kFourAtlas_fires_of_wall_heavyCap (point : DirectionChartPoint 6)
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
    (hw0 : 16 * point.weight 0 ≤ 3) (hw1 : 16 * point.weight 1 ≤ 3)
    (hw4 : 16 * point.weight 4 ≤ 3) (hw5 : 16 * point.weight 5 ≤ 3) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inl
    (kFourStarACell_fires_of_wall_heavyCap point hz0 hz1 hz2 hs hm0 hm1 hm2
      hd3 hd4 hd5 hmax1 hmax2 hw0 hw1 hw4 hw5)))))

end Gtz
