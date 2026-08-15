import Gtz.Design.StarWallHeavyCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The sharp weight cap of the gauge star wall

The landed balanced case of the gauge star wall asks every sensitive weight to
be at most `1/6`, and the heavy case raises the cap to `3/16`.  Both proofs
bound each negative term of the determinant against one master monomial.  That
architecture stalls before the true wall threshold.

This module replaces the term bound by a joint bound and reaches the exact
threshold.  Write `kap` for the boost quotient `(1 - w) / w` of a cap `w`.  The
determinant of the vertex-a cell at the worst demands is

  `kap ^ 3 * det = kap * s ^ 3 * z 1 * z 2 * (z 0 + z 1 + z 2) * V`,

where `V` collects five terms whose coefficients are

  `(kap ^ 2 - 4 * kap + 1) * (kap ^ 2 - 3)`, `2 * (kap - 1) * (kap ^ 2 - 5)`,
  `(kap + 3) * (kap - 1)`, `2 * (kap ^ 2 + 2 * kap - 9)` and `4`.

Every coefficient is positive exactly when `kap ^ 2 - 4 * kap + 1` is positive,
which is the threshold `kap > 2 + √3`, that is a cap below `(3 - √3) / 6`.

* `starWall_sharp_corner`, `starWall_sharp_minorTwo` and `starWall_sharp_det`
  are the three scalar minors at a general cap.
* `kFourStarACell_fires_of_wall_sharpCap` is the chart form, and
  `kFourAtlas_fires_of_wall_sharpCap` fires the full minor atlas.
* `kFourAtlas_fires_of_wall_fifthCap` is the cap `1/5`, and
  `kFourAtlas_fires_of_wall_nineteenthCap` is the cap `4/19`.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The three scalar positivity facts of the wall family -/

/-- The two inside boost gaps and the outside gap of the wall family are
positive.  Every bound spends only the axis order and the cap floor `3`. -/
theorem starWall_sharp_gaps {kap a b c : ℝ} (ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hba : b ≤ a) (hca : c ≤ a) (hk3 : 3 ≤ kap) :
    0 < kap ^ 2 * a - kap * c - (a + b + c)
      ∧ 0 < kap ^ 2 * a - kap * b - (a + b + c)
      ∧ 0 < kap * a - b - c := by
  have hL : (3:ℝ) ≤ kap ^ 2 - kap - 3 := by nlinarith
  have hLa : a * 3 ≤ a * (kap ^ 2 - kap - 3) := mul_le_mul_of_nonneg_left hL ha.le
  refine ⟨?_, ?_, by nlinarith⟩
  · nlinarith [mul_le_mul_of_nonneg_left hca (by linarith : (0:ℝ) ≤ kap), hLa]
  · nlinarith [mul_le_mul_of_nonneg_left hba (by linarith : (0:ℝ) ≤ kap), hLa]

/-- The three products the joint bound needs.  The first is strict, because the
second minor of the cell reads exactly zero at the boost quotient `3`.  Each
bound spends the axis order and the cap floor against the boost gaps. -/
theorem starWall_sharp_sides {kap a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hba : b ≤ a) (hca : c ≤ a) (hk3s : 3 < kap) :
    kap ^ 2 * (b * c)
        < (kap ^ 2 * a - kap * c - (a + b + c)) * (kap ^ 2 * a - kap * b - (a + b + c))
      ∧ c * (a + b + c)
        ≤ (kap * a - b - c) * (kap ^ 2 * a - kap * b - (a + b + c))
      ∧ b * (a + b + c)
        ≤ (kap * a - b - c) * (kap ^ 2 * a - kap * c - (a + b + c)) := by
  have hk3 : (3:ℝ) ≤ kap := le_of_lt hk3s
  obtain ⟨hga, hgb, hgc⟩ := starWall_sharp_gaps ha hb hc hba hca hk3
  have hkpos : (0:ℝ) < kap := by linarith
  -- the common lower bounds of the three gaps
  have hthree : (3:ℝ) ≤ kap ^ 2 - kap - 3 := by nlinarith
  have hposk : (0:ℝ) < kap ^ 2 - kap - 3 := by linarith
  have hLa : a * 3 ≤ a * (kap ^ 2 - kap - 3) := mul_le_mul_of_nonneg_left hthree ha.le
  have hlowA : (kap ^ 2 - kap - 3) * a ≤ kap ^ 2 * a - kap * c - (a + b + c) := by
    nlinarith [mul_le_mul_of_nonneg_left hca (by linarith : (0:ℝ) ≤ kap)]
  have hlowB : (kap ^ 2 - kap - 3) * a ≤ kap ^ 2 * a - kap * b - (a + b + c) := by
    nlinarith [mul_le_mul_of_nonneg_left hba (by linarith : (0:ℝ) ≤ kap)]
  have hlowC : a ≤ kap * a - b - c := by nlinarith
  have hbc : b * c ≤ a * a := mul_le_mul hba hca hc.le ha.le
  have hprodAB : ((kap ^ 2 - kap - 3) * a) * ((kap ^ 2 - kap - 3) * a)
      ≤ (kap ^ 2 * a - kap * c - (a + b + c)) * (kap ^ 2 * a - kap * b - (a + b + c)) :=
    mul_le_mul hlowA hlowB (by positivity) (le_of_lt hga)
  refine ⟨?_, ?_, ?_⟩
  · -- the strict product: the gap bound beats `kap` itself once `kap` passes three
    have hkbig : kap < kap ^ 2 - kap - 3 := by nlinarith
    have hsq : kap ^ 2 < (kap ^ 2 - kap - 3) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hkbig) (by linarith : (0:ℝ) < kap ^ 2 - kap - 3 + kap)]
    have h1 : kap ^ 2 * (b * c) ≤ kap ^ 2 * (a * a) :=
      mul_le_mul_of_nonneg_left hbc (by positivity)
    have h2 : kap ^ 2 * (a * a) < (kap ^ 2 - kap - 3) ^ 2 * (a * a) := by
      have haa : (0:ℝ) < a * a := by positivity
      nlinarith [hsq, haa]
    nlinarith [h1, h2, hprodAB]
  · have hcS : c * (a + b + c) ≤ 3 * (a * a) := by nlinarith
    nlinarith [mul_le_mul hlowC hlowB (by positivity) (by linarith : (0:ℝ) ≤ kap * a - b - c),
      hLa, hcS]
  · have hbS : b * (a + b + c) ≤ 3 * (a * a) := by nlinarith
    nlinarith [mul_le_mul hlowC hlowA (by positivity) (by linarith : (0:ℝ) ≤ kap * a - b - c),
      hLa, hbS]

/-- The sharp wall polynomial is positive.  Every coefficient is positive
exactly at the threshold `kap ^ 2 - 4 * kap + 1 > 0`. -/
theorem starWall_sharp_poly {kap a b c : ℝ} (ha : 0 < a) (hba : b ≤ a) (hca : c ≤ a)
    (hk3 : 3 ≤ kap) (hsharp : 4 * kap < kap ^ 2 + 1) :
    0 < a ^ 3 * ((kap ^ 2 - 4 * kap + 1) * (kap ^ 2 - 3))
      + 2 * a ^ 2 * ((a - b) + (a - c)) * ((kap - 1) * (kap ^ 2 - 5))
      + a * ((kap + 3) * (kap - 1)) * ((a - b) ^ 2 + (a - c) ^ 2)
      + 2 * a * (kap ^ 2 + 2 * kap - 9) * ((a - b) * (a - c))
      + 4 * ((a - b) * (a - c)) * ((a - b) + (a - c)) := by
  have hp : (0:ℝ) ≤ a - b := by linarith
  have hq : (0:ℝ) ≤ a - c := by linarith
  have h1 : (0:ℝ) < (kap ^ 2 - 4 * kap + 1) * (kap ^ 2 - 3) := by
    have : (0:ℝ) < kap ^ 2 - 4 * kap + 1 := by linarith
    have : (0:ℝ) < kap ^ 2 - 3 := by nlinarith
    positivity
  have h2 : (0:ℝ) ≤ (kap - 1) * (kap ^ 2 - 5) := by nlinarith
  have h3 : (0:ℝ) ≤ (kap + 3) * (kap - 1) := by nlinarith
  have h4 : (0:ℝ) ≤ kap ^ 2 + 2 * kap - 9 := by nlinarith
  have t1 : (0:ℝ) < a ^ 3 * ((kap ^ 2 - 4 * kap + 1) * (kap ^ 2 - 3)) := by positivity
  have t2 : (0:ℝ) ≤ 2 * a ^ 2 * ((a - b) + (a - c)) * ((kap - 1) * (kap ^ 2 - 5)) := by positivity
  have t3 : (0:ℝ) ≤ a * ((kap + 3) * (kap - 1)) * ((a - b) ^ 2 + (a - c) ^ 2) := by positivity
  have t4 : (0:ℝ) ≤ 2 * a * (kap ^ 2 + 2 * kap - 9) * ((a - b) * (a - c)) := by positivity
  have t5 : (0:ℝ) ≤ 4 * ((a - b) * (a - c)) * ((a - b) + (a - c)) := by positivity
  linarith

/-! ## 2. The three minors at a general cap -/

/-- **THE CORNER.**  The first inside gap of the vertex-a cell is positive at
every cap with boost quotient at least `3`. -/
theorem starWall_sharp_corner {kap a b c S m4 : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hS : 0 < S) (hba : b ≤ a) (hca : c ≤ a) (hk3 : 3 ≤ kap)
    (hcap4 : kap * m4 ≤ S * (b * (a + b + c))) :
    0 < kap * (S * (a * b)) - S * (b * c) - m4 := by
  obtain ⟨hga, -, -⟩ := starWall_sharp_gaps ha hb hc hba hca hk3
  have hkpos : (0:ℝ) < kap := by linarith
  have hkey : 0 < kap * (kap * (S * (a * b)) - S * (b * c) - m4) := by
    have hlow : S * (b * (kap ^ 2 * a - kap * c - (a + b + c)))
        ≤ kap * (kap * (S * (a * b)) - S * (b * c) - m4) := by nlinarith [hcap4]
    have : 0 < S * (b * (kap ^ 2 * a - kap * c - (a + b + c))) := by positivity
    linarith
  nlinarith [hkey, hkpos]

/-- The wall threshold puts the boost quotient strictly above three. -/
theorem starWall_sharp_gt_three {kap : ℝ} (hk3 : 3 ≤ kap) (hsharp : 4 * kap < kap ^ 2 + 1) :
    3 < kap := by
  rcases lt_or_eq_of_le hk3 with h | h
  · exact h
  · exfalso; rw [← h] at hsharp; norm_num at hsharp

/-- **THE SECOND MINOR.**  The two inside gaps beat the shared outside mass.
The threshold is load-bearing: at the boost quotient `3` this minor reads
exactly zero on the symmetric axis. -/
theorem starWall_sharp_minorTwo {kap a b c S m4 m5 : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hS : 0 < S) (hba : b ≤ a) (hca : c ≤ a) (hk3 : 3 ≤ kap)
    (hsharp : 4 * kap < kap ^ 2 + 1)
    (hcap4 : kap * m4 ≤ S * (b * (a + b + c))) (hcap5 : kap * m5 ≤ S * (c * (a + b + c))) :
    0 < (kap * (S * (a * b)) - S * (b * c) - m4) * (kap * (S * (a * c)) - S * (b * c) - m5)
      - (S * (b * c)) ^ 2 := by
  have hk3s := starWall_sharp_gt_three hk3 hsharp
  obtain ⟨hga, hgb, -⟩ := starWall_sharp_gaps ha hb hc hba hca hk3
  obtain ⟨hS1, -, -⟩ := starWall_sharp_sides ha hb hc hba hca hk3s
  have hkpos : (0:ℝ) < kap := by linarith
  have hlowA : S * (b * (kap ^ 2 * a - kap * c - (a + b + c)))
      ≤ kap * (kap * (S * (a * b)) - S * (b * c) - m4) := by nlinarith [hcap4]
  have hlowB : S * (c * (kap ^ 2 * a - kap * b - (a + b + c)))
      ≤ kap * (kap * (S * (a * c)) - S * (b * c) - m5) := by nlinarith [hcap5]
  have hposA : 0 < S * (b * (kap ^ 2 * a - kap * c - (a + b + c))) := by positivity
  have hposB : 0 < S * (c * (kap ^ 2 * a - kap * b - (a + b + c))) := by positivity
  have hprod : (S * (b * (kap ^ 2 * a - kap * c - (a + b + c))))
        * (S * (c * (kap ^ 2 * a - kap * b - (a + b + c))))
      ≤ (kap * (kap * (S * (a * b)) - S * (b * c) - m4))
        * (kap * (kap * (S * (a * c)) - S * (b * c) - m5)) :=
    mul_le_mul hlowA hlowB hposB.le (by linarith)
  have hgap : 0 < (S * (b * (kap ^ 2 * a - kap * c - (a + b + c))))
      * (S * (c * (kap ^ 2 * a - kap * b - (a + b + c)))) - kap ^ 2 * (S * (b * c)) ^ 2 := by
    have hid : (S * (b * (kap ^ 2 * a - kap * c - (a + b + c))))
          * (S * (c * (kap ^ 2 * a - kap * b - (a + b + c)))) - kap ^ 2 * (S * (b * c)) ^ 2
        = (S * S * (b * c))
          * ((kap ^ 2 * a - kap * c - (a + b + c)) * (kap ^ 2 * a - kap * b - (a + b + c))
            - kap ^ 2 * (b * c)) := by ring
    have hpos : 0 < (S * S * (b * c))
        * ((kap ^ 2 * a - kap * c - (a + b + c)) * (kap ^ 2 * a - kap * b - (a + b + c))
          - kap ^ 2 * (b * c)) := mul_pos (by positivity) (by linarith)
    linarith [hid, hpos]
  have hkey : 0 < kap ^ 2 * ((kap * (S * (a * b)) - S * (b * c) - m4)
      * (kap * (S * (a * c)) - S * (b * c) - m5) - (S * (b * c)) ^ 2) := by
    nlinarith [hprod, hgap]
  nlinarith [hkey, hkpos]


/-- **THE CLEARING IDENTITY.**  The worst-demand determinant of the vertex-a
cell, scaled by the cube of the boost quotient, is the sharp wall polynomial
times the two triangle axes and the axis sum. -/
theorem starWall_sharp_identity (kap a b c S : ℝ) :
    (S * ((a + b + c) * (kap * a - b - c)))
        * ((S * (b * (kap ^ 2 * a - kap * c - (a + b + c))))
            * (S * (c * (kap ^ 2 * a - kap * b - (a + b + c))))
          - kap ^ 2 * (S * (b * c)) ^ 2)
      - (S * (b * (kap ^ 2 * a - kap * c - (a + b + c)))) * (S * (c * (a + b + c))) ^ 2
      - 2 * kap * (S * (b * c)) * ((S * (b * (a + b + c))) * (S * (c * (a + b + c))))
      - (S * (c * (kap ^ 2 * a - kap * b - (a + b + c)))) * (S * (b * (a + b + c))) ^ 2
    = kap * (S ^ 3 * (b * (c * ((a + b + c)
        * (a ^ 3 * ((kap ^ 2 - 4 * kap + 1) * (kap ^ 2 - 3))
          + 2 * a ^ 2 * ((a - b) + (a - c)) * ((kap - 1) * (kap ^ 2 - 5))
          + a * ((kap + 3) * (kap - 1)) * ((a - b) ^ 2 + (a - c) ^ 2)
          + 2 * a * (kap ^ 2 + 2 * kap - 9) * ((a - b) * (a - c))
          + 4 * ((a - b) * (a - c)) * ((a - b) + (a - c))))))) := by
  ring

/-- **THE DETERMINANT, JOINTLY BOUNDED.**  The determinant of the vertex-a cell
is positive at every cap whose boost quotient is at least three and clears the
wall threshold.  The negative block is bounded once, against the whole product,
rather than term by term.  That is what reaches the threshold. -/
theorem starWall_sharp_det {kap a b c S m4 m5 : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hS : 0 < S) (hba : b ≤ a) (hca : c ≤ a) (hk3 : 3 ≤ kap)
    (hsharp : 4 * kap < kap ^ 2 + 1) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (hcap4 : kap * m4 ≤ S * (b * (a + b + c))) (hcap5 : kap * m5 ≤ S * (c * (a + b + c))) :
    0 < (kap * (S * (a * b)) - S * (b * c) - m4) * (kap * (S * (a * c)) - S * (b * c) - m5)
          * (S * (a * (a + b + c)) - m4 - m5)
        - (kap * (S * (a * b)) - S * (b * c) - m4) * m5 ^ 2
        - (S * (b * c)) ^ 2 * (S * (a * (a + b + c)) - m4 - m5)
        - 2 * (S * (b * c)) * m4 * m5
        - m4 ^ 2 * (kap * (S * (a * c)) - S * (b * c) - m5) := by
  have hk3s := starWall_sharp_gt_three hk3 hsharp
  obtain ⟨hga, hgb, hgc⟩ := starWall_sharp_gaps ha hb hc hba hca hk3
  obtain ⟨hS1', hS2, hS3⟩ := starWall_sharp_sides ha hb hc hba hca hk3s
  have hkpos : (0:ℝ) < kap := by linarith
  have hS1 : kap ^ 2 * (b * c)
      ≤ (kap ^ 2 * a - kap * c - (a + b + c)) * (kap ^ 2 * a - kap * b - (a + b + c)) :=
    le_of_lt hS1'
  have hSpos : (0:ℝ) < S * S := by positivity
  have hAsPos : (0:ℝ) < S * (b * (kap ^ 2 * a - kap * c - (a + b + c))) := by positivity
  have hBsPos : (0:ℝ) < S * (c * (kap ^ 2 * a - kap * b - (a + b + c))) := by positivity
  have hCsPos : (0:ℝ) < S * ((a + b + c) * (kap * a - b - c)) := by positivity
  have hN4Pos : (0:ℝ) < S * (b * (a + b + c)) := by positivity
  have hN5Pos : (0:ℝ) < S * (c * (a + b + c)) := by positivity
  have hm2Pos : (0:ℝ) < S * (b * c) := by positivity
  have hP4pos : (0:ℝ) < kap * m4 := by positivity
  have hP5pos : (0:ℝ) < kap * m5 := by positivity
  have hAlow : S * (b * (kap ^ 2 * a - kap * c - (a + b + c)))
      ≤ kap * (kap * (S * (a * b)) - S * (b * c) - m4) := by nlinarith [hcap4]
  have hBlow : S * (c * (kap ^ 2 * a - kap * b - (a + b + c)))
      ≤ kap * (kap * (S * (a * c)) - S * (b * c) - m5) := by nlinarith [hcap5]
  have hClow : S * ((a + b + c) * (kap * a - b - c))
      ≤ kap * (S * (a * (a + b + c)) - m4 - m5) := by nlinarith [hcap4, hcap5]
  have hApos : (0:ℝ) < kap * (kap * (S * (a * b)) - S * (b * c) - m4) :=
    lt_of_lt_of_le hAsPos hAlow
  have hBpos : (0:ℝ) < kap * (kap * (S * (a * c)) - S * (b * c) - m5) :=
    lt_of_lt_of_le hBsPos hBlow
  have hCpos : (0:ℝ) < kap * (S * (a * (a + b + c)) - m4 - m5) :=
    lt_of_lt_of_le hCsPos hClow
  have hside1 : kap ^ 2 * (S * (b * c)) ^ 2
      ≤ (S * (b * (kap ^ 2 * a - kap * c - (a + b + c))))
        * (S * (c * (kap ^ 2 * a - kap * b - (a + b + c)))) := by
    nlinarith [mul_le_mul_of_nonneg_left hS1 hSpos.le]
  have hside2 : (S * (c * (a + b + c))) ^ 2
      ≤ (S * ((a + b + c) * (kap * a - b - c)))
        * (S * (c * (kap ^ 2 * a - kap * b - (a + b + c)))) := by
    nlinarith [mul_le_mul_of_nonneg_left hS2 hSpos.le]
  have hside3 : (S * (b * (a + b + c))) ^ 2
      ≤ (S * ((a + b + c) * (kap * a - b - c)))
        * (S * (b * (kap ^ 2 * a - kap * c - (a + b + c)))) := by
    nlinarith [mul_le_mul_of_nonneg_left hS3 hSpos.le]
  have hworst : 0 < (S * ((a + b + c) * (kap * a - b - c)))
        * ((S * (b * (kap ^ 2 * a - kap * c - (a + b + c))))
            * (S * (c * (kap ^ 2 * a - kap * b - (a + b + c))))
          - kap ^ 2 * (S * (b * c)) ^ 2)
      - (S * (b * (kap ^ 2 * a - kap * c - (a + b + c)))) * (S * (c * (a + b + c))) ^ 2
      - 2 * kap * (S * (b * c)) * ((S * (b * (a + b + c))) * (S * (c * (a + b + c))))
      - (S * (c * (kap ^ 2 * a - kap * b - (a + b + c)))) * (S * (b * (a + b + c))) ^ 2 := by
    rw [starWall_sharp_identity kap a b c S]
    have hpoly := starWall_sharp_poly ha hba hca hk3 hsharp
    positivity
  -- the chain, in the scaled quantities
  set A := kap * (kap * (S * (a * b)) - S * (b * c) - m4) with hA
  set B := kap * (kap * (S * (a * c)) - S * (b * c) - m5) with hB
  set C := kap * (S * (a * (a + b + c)) - m4 - m5) with hC
  set As := S * (b * (kap ^ 2 * a - kap * c - (a + b + c))) with hAs
  set Bs := S * (c * (kap ^ 2 * a - kap * b - (a + b + c))) with hBs
  set Cs := S * ((a + b + c) * (kap * a - b - c)) with hCs
  set N4 := S * (b * (a + b + c)) with hN4
  set N5 := S * (c * (a + b + c)) with hN5
  set m2 := S * (b * c) with hm2
  have hABm : kap ^ 2 * m2 ^ 2 ≤ A * B :=
    le_trans hside1 (mul_le_mul hAlow hBlow hBsPos.le hApos.le)
  have hstep1 : Cs * (A * B - kap ^ 2 * m2 ^ 2) - A * N5 ^ 2 - 2 * kap * m2 * (N4 * N5)
        - B * N4 ^ 2
      ≤ A * B * C - A * (kap * m5) ^ 2 - kap ^ 2 * m2 ^ 2 * C
        - 2 * kap * m2 * (kap * m4 * (kap * m5)) - (kap * m4) ^ 2 * B := by
    have h1 : Cs * (A * B - kap ^ 2 * m2 ^ 2) ≤ C * (A * B - kap ^ 2 * m2 ^ 2) :=
      mul_le_mul_of_nonneg_right hClow (by linarith)
    have h2 : A * (kap * m5) ^ 2 ≤ A * N5 ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith [hcap5, hP5pos]) hApos.le
    have h3 : (kap * m4) ^ 2 * B ≤ N4 ^ 2 * B :=
      mul_le_mul_of_nonneg_right (by nlinarith [hcap4, hP4pos]) hBpos.le
    have h4 : 2 * kap * m2 * (kap * m4 * (kap * m5)) ≤ 2 * kap * m2 * (N4 * N5) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hcap4 hcap5 hP5pos.le hN4Pos.le) (by positivity)
    nlinarith [h1, h2, h3, h4]
  have hstep2 : Cs * (As * Bs - kap ^ 2 * m2 ^ 2) - As * N5 ^ 2 - 2 * kap * m2 * (N4 * N5)
        - Bs * N4 ^ 2
      ≤ Cs * (A * B - kap ^ 2 * m2 ^ 2) - A * N5 ^ 2 - 2 * kap * m2 * (N4 * N5)
        - B * N4 ^ 2 := by
    have hone : 0 ≤ (A - As) * (Cs * B - N5 ^ 2) :=
      mul_nonneg (by linarith)
        (by linarith [le_trans hside2 (mul_le_mul_of_nonneg_left hBlow hCsPos.le)])
    have htwo : 0 ≤ (B - Bs) * (Cs * As - N4 ^ 2) :=
      mul_nonneg (by linarith) (by linarith [hside3])
    have hid : Cs * (A * B - kap ^ 2 * m2 ^ 2) - A * N5 ^ 2 - 2 * kap * m2 * (N4 * N5)
          - B * N4 ^ 2
        - (Cs * (As * Bs - kap ^ 2 * m2 ^ 2) - As * N5 ^ 2 - 2 * kap * m2 * (N4 * N5)
          - Bs * N4 ^ 2)
        = (A - As) * (Cs * B - N5 ^ 2) + (B - Bs) * (Cs * As - N4 ^ 2) := by ring
    linarith [hone, htwo, hid]
  have hscaledPos : 0 < A * B * C - A * (kap * m5) ^ 2 - kap ^ 2 * m2 ^ 2 * C
      - 2 * kap * m2 * (kap * m4 * (kap * m5)) - (kap * m4) ^ 2 * B := by
    linarith [hstep1, hstep2, hworst]
  have hexpand : A * B * C - A * (kap * m5) ^ 2 - kap ^ 2 * m2 ^ 2 * C
      - 2 * kap * m2 * (kap * m4 * (kap * m5)) - (kap * m4) ^ 2 * B
      = kap ^ 3 * ((kap * (S * (a * b)) - m2 - m4)
            * (kap * (S * (a * c)) - m2 - m5)
            * (S * (a * (a + b + c)) - m4 - m5)
          - (kap * (S * (a * b)) - m2 - m4) * m5 ^ 2
          - m2 ^ 2 * (S * (a * (a + b + c)) - m4 - m5)
          - 2 * m2 * m4 * m5
          - m4 ^ 2 * (kap * (S * (a * c)) - m2 - m5)) := by
    rw [hA, hB, hC]; ring
  rw [hexpand] at hscaledPos
  have hk3pos : (0:ℝ) < kap ^ 3 := by positivity
  by_contra hcon
  push Not at hcon
  nlinarith [hscaledPos, hk3pos, hcon]

/-! ## 3. The chart form and the two named caps -/

/-- **THE SHARP CAP OF THE VERTEX-A CELL.**  On the gauge star wall with the
maximal axis at slot zero, every sensitive weight cap whose boost quotient
clears the wall threshold fires the vertex-a cell. -/
theorem kFourStarACell_fires_of_wall_sharpCap (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s kap : ℝ}
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
    (hk3 : 3 ≤ kap) (hsharp : 4 * kap < kap ^ 2 + 1)
    (hw0 : point.weight 0 * (kap + 1) ≤ 1) (hw1 : point.weight 1 * (kap + 1) ≤ 1)
    (hw4 : point.weight 4 * (kap + 1) ≤ 1) (hw5 : point.weight 5 * (kap + 1) ≤ 1) :
    KFourUnsignedStarACellFires point := by
  have hw0pos := point.weight_pos 0
  have hw1pos := point.weight_pos 1
  have hw4pos := point.weight_pos 4
  have hw5pos := point.weight_pos 5
  have hm4pos := point.mass_pos 4
  have hm5pos := point.mass_pos 5
  have hkpos : (0:ℝ) < kap := by linarith
  have hcap4 : kap * point.mass 4 ≤ s * (z 1 * (z 0 + z 1 + z 2)) := by
    have hstep : (kap * point.mass 4) * point.weight 4
        ≤ (s * (z 1 * (z 0 + z 1 + z 2))) * point.weight 4 := by nlinarith [hd4, hm4pos]
    exact le_of_mul_le_mul_right hstep hw4pos
  have hcap5 : kap * point.mass 5 ≤ s * (z 2 * (z 0 + z 1 + z 2)) := by
    have hstep : (kap * point.mass 5) * point.weight 5
        ≤ (s * (z 2 * (z 0 + z 1 + z 2))) * point.weight 5 := by nlinarith [hd5, hm5pos]
    exact le_of_mul_le_mul_right hstep hw5pos
  have hcorner := starWall_sharp_corner hz0 hz1 hz2 hs hmax1 hmax2 hk3 hcap4
  have hminorTwo := starWall_sharp_minorTwo hz0 hz1 hz2 hs hmax1 hmax2 hk3 hsharp hcap4 hcap5
  have hdet := starWall_sharp_det hz0 hz1 hz2 hs hmax1 hmax2 hk3 hsharp hm4pos hm5pos hcap4 hcap5
  refine ⟨kap * (s * (z 0 * z 1)), kap * (s * (z 0 * z 2)),
    s * (z 0 * (z 0 + z 1 + z 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm0]; nlinarith [mul_pos hs (mul_pos hz0 hz1), hw0pos]
  · rw [hm1]; nlinarith [mul_pos hs (mul_pos hz0 hz2), hw1pos]
  · rw [hd3]
  · rw [hm2]; linarith [hcorner]
  · rw [hm2]; nlinarith [hminorTwo]
  · rw [hm2]; nlinarith [hdet]

/-- The sharp-cap wall case fires the full minor atlas. -/
theorem kFourAtlas_fires_of_wall_sharpCap (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s kap : ℝ}
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
    (hk3 : 3 ≤ kap) (hsharp : 4 * kap < kap ^ 2 + 1)
    (hw0 : point.weight 0 * (kap + 1) ≤ 1) (hw1 : point.weight 1 * (kap + 1) ≤ 1)
    (hw4 : point.weight 4 * (kap + 1) ≤ 1) (hw5 : point.weight 5 * (kap + 1) ≤ 1) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inl
    (kFourStarACell_fires_of_wall_sharpCap point hz0 hz1 hz2 hs hm0 hm1 hm2
      hd3 hd4 hd5 hmax1 hmax2 hk3 hsharp hw0 hw1 hw4 hw5)))))

/-- The cap `1/5`.  The boost quotient is `4`, which the term bound of the heavy
case cannot reach. -/
theorem kFourAtlas_fires_of_wall_fifthCap (point : DirectionChartPoint 6)
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
    (hw0 : 5 * point.weight 0 ≤ 1) (hw1 : 5 * point.weight 1 ≤ 1)
    (hw4 : 5 * point.weight 4 ≤ 1) (hw5 : 5 * point.weight 5 ≤ 1) :
    KFourAllTreeMinorAtlasCellFires point :=
  kFourAtlas_fires_of_wall_sharpCap point (kap := 4) hz0 hz1 hz2 hs hm0 hm1 hm2
    hd3 hd4 hd5 hmax1 hmax2 (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by linarith) (by linarith)

/-- The cap `4/19`.  The boost quotient is `15/4`, inside the exact wall
threshold `2 + √3`, and the widest named cap of the campaign. -/
theorem kFourAtlas_fires_of_wall_nineteenthCap (point : DirectionChartPoint 6)
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
    (hw0 : 19 * point.weight 0 ≤ 4) (hw1 : 19 * point.weight 1 ≤ 4)
    (hw4 : 19 * point.weight 4 ≤ 4) (hw5 : 19 * point.weight 5 ≤ 4) :
    KFourAllTreeMinorAtlasCellFires point :=
  kFourAtlas_fires_of_wall_sharpCap point (kap := 15 / 4) hz0 hz1 hz2 hs hm0 hm1 hm2
    hd3 hd4 hd5 hmax1 hmax2 (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by linarith) (by linarith)

end Gtz
