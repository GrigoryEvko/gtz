import Gtz.Design.StarWallSharpCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The joint firing region of the gauge star wall

The landed caps of the gauge star wall are boxes.  The balanced case asks every
sensitive weight to be at most `1/6`, the heavy case `3/16`, and the sharp case
the exact threshold `(3 - √3) / 6`.  All three ask the *same* bound of all four
sensitive weights, and all three bound the boost quotient of each weight by one
shared number.  The true firing region is not a box.

The four sensitive labels enter the vertex-a cell differently.  Labels `0` and
`1` enter only through their own boost quotients, and labels `4` and `5` enter
only through the dust fractions `p` and `q` that their masses cut out of the
pinned floors.  This module carries the four parameters separately and reads the
three minors of the cell in the wall coordinates

  `al = k0 * a - c - S * p`,  `be = k1 * a - b - S * q`,  `ga = a - b * p - c * q`,

where `a`, `b`, `c` are the axis with `a` maximal and `S = a + b + c`.  The three
minors then are

  `0 < al`,  `b * c < al * be`,
  `S * (c * q ^ 2 * al + b * p ^ 2 * be + 2 * (b * c) * (p * q)) < ga * (al * be - b * c)`.

* `starWall_joint_minorTwo` and `starWall_joint_det` are the two clearing
  identities and their positivity.
* `kFourStarACell_fires_of_wall_jointCondition` is the chart form.  It carries
  the two inside boost quotients and the two dust fractions separately, and it
  contains every landed cap as the diagonal slice.
* `kFourAtlas_fires_of_wall_quarterEighth` and
  `kFourAtlas_fires_of_wall_threeTenthTwentyFirst` are two named instances that
  lie strictly outside the sharp box: the first allows the weights `0` and `1`
  the value `1/4`, and the second the value `3/10`, both above the sharp cap
  `(3 - √3) / 6 < 0.212`.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The two clearing identities -/

/-- **THE SECOND MINOR.**  In the wall coordinates the second minor of the
vertex-a cell is the axis product times the gap `al * be - b * c`. -/
theorem starWall_joint_minorTwo {b c s al be : ℝ} (hb : 0 < b) (hc : 0 < c) (hs : 0 < s)
    (hgap : b * c < al * be) :
    0 < (s * (b * al)) * (s * (c * be)) - (s * (b * c)) ^ 2 := by
  have hid : (s * (b * al)) * (s * (c * be)) - (s * (b * c)) ^ 2
      = s ^ 2 * (b * c) * (al * be - b * c) := by ring
  rw [hid]
  have hpos : (0:ℝ) < s ^ 2 * (b * c) := by positivity
  have hsub : (0:ℝ) < al * be - b * c := by linarith
  positivity

/-- **THE DETERMINANT.**  In the wall coordinates the determinant of the
vertex-a cell is the axis product, the axis sum, and the joint gap

  `ga * (al * be - b * c) - S * (c * q ^ 2 * al + b * p ^ 2 * be + 2 * b * c * p * q)`.

The dust fractions `p` and `q` enter only through that one quadratic form, which
is what lets the two inside boost quotients and the two dust fractions move
independently. -/
theorem starWall_joint_det {a b c s al be ga p q : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hs : 0 < s) (hS : 0 < a + b + c)
    (hjoint : (a + b + c) * (c * q ^ 2 * al + b * p ^ 2 * be + 2 * (b * c) * (p * q))
      < ga * (al * be - b * c)) :
    0 < (s * (b * al)) * (s * (c * be)) * (s * ((a + b + c) * ga))
        - (s * (b * al)) * (s * (c * ((a + b + c) * q))) ^ 2
        - (s * (b * c)) ^ 2 * (s * ((a + b + c) * ga))
        - 2 * (s * (b * c)) * (s * (b * ((a + b + c) * p)))
            * (s * (c * ((a + b + c) * q)))
        - (s * (b * ((a + b + c) * p))) ^ 2 * (s * (c * be)) := by
  have hid : (s * (b * al)) * (s * (c * be)) * (s * ((a + b + c) * ga))
        - (s * (b * al)) * (s * (c * ((a + b + c) * q))) ^ 2
        - (s * (b * c)) ^ 2 * (s * ((a + b + c) * ga))
        - 2 * (s * (b * c)) * (s * (b * ((a + b + c) * p)))
            * (s * (c * ((a + b + c) * q)))
        - (s * (b * ((a + b + c) * p))) ^ 2 * (s * (c * be))
      = s ^ 3 * (b * (c * (a + b + c)))
          * (ga * (al * be - b * c)
            - (a + b + c) * (c * q ^ 2 * al + b * p ^ 2 * be + 2 * (b * c) * (p * q))) := by
    ring
  rw [hid]
  have hpos : (0:ℝ) < s ^ 3 * (b * (c * (a + b + c))) := by positivity
  have hsub : (0:ℝ) < ga * (al * be - b * c)
      - (a + b + c) * (c * q ^ 2 * al + b * p ^ 2 * be + 2 * (b * c) * (p * q)) := by
    linarith
  positivity

/-! ## 2. The two axis keys -/

/-- Two lower bounds on the inside gaps beat the axis product. -/
theorem starWall_joint_gap_of_bounds {z0 al be bc L : ℝ} (hz0 : 0 < z0) (hL : 1 < L)
    (hal : L * z0 ≤ al) (hbe : L * z0 ≤ be) (hbc : bc ≤ z0 * z0) :
    bc < al * be := by
  have hLz : (0:ℝ) < L * z0 := by positivity
  have h : (L * z0) * (L * z0) ≤ al * be :=
    mul_le_mul hal hbe hLz.le (le_trans hLz.le hal)
  have hL2 : (1:ℝ) < L * L := by nlinarith [hL]
  have hstrict : 1 * (z0 * z0) < (L * L) * (z0 * z0) :=
    mul_lt_mul_of_pos_right hL2 (mul_pos hz0 hz0)
  have hrw : (L * z0) * (L * z0) = (L * L) * (z0 * z0) := by ring
  rw [hrw] at h
  linarith

/-- **THE AXIS KEY OF THE QUARTER CAP.**  The gap bound `11 * z0 ≤ 7 * gap`
carries the joint inequality with the room `36 * z0 ^ 2`. -/
theorem starWall_joint_key_quarter {z0 al be bc : ℝ} (hz0 : 0 < z0)
    (hal : 11 * z0 ≤ 7 * al) (hbe : 11 * z0 ≤ 7 * be) (hbc : bc ≤ z0 * z0) :
    3 * z0 * (al + be + 2 * z0) < 35 * (al * be - bc) := by
  have hsq : (0:ℝ) ≤ (7 * al - 11 * z0) * (7 * be - 11 * z0) :=
    mul_nonneg (by linarith) (by linarith)
  have hlin : (0:ℝ) ≤ z0 * (al + be - 22 / 7 * z0) := mul_nonneg hz0.le (by linarith)
  nlinarith [hsq, hlin, hbc, mul_pos hz0 hz0]

/-- **THE AXIS KEY OF THE THREE-TENTH CAP.**  The weaker gap bound
`71 * z0 ≤ 60 * gap` still carries the joint inequality, because the dust cap
`1 / 20` shrinks the negative block by the square. -/
theorem starWall_joint_key_threeTenth {z0 al be bc : ℝ} (hz0 : 0 < z0)
    (hal : 71 * z0 ≤ 60 * al) (hbe : 71 * z0 ≤ 60 * be) (hbc : bc ≤ z0 * z0) :
    z0 * (al + be + 2 * z0) < 120 * (al * be - bc) := by
  have hsq : (0:ℝ) ≤ (60 * al - 71 * z0) * (60 * be - 71 * z0) :=
    mul_nonneg (by linarith) (by linarith)
  have hlin : (0:ℝ) ≤ z0 * (al + be - 71 / 30 * z0) := mul_nonneg hz0.le (by linarith)
  nlinarith [hsq, hlin, hbc, mul_pos hz0 hz0]

/-! ## 3. The joint chart condition -/

/-- **THE JOINT FIRING CONDITION OF THE VERTEX-A CELL.**  On the gauge star wall
with the maximal axis at slot zero, the vertex-a cell fires as soon as the three
minors read positively in the wall coordinates.

The two inside boost quotients `k0` and `k1` and the two dust fractions `p` and
`q` are independent.  Every landed cap is the slice `k0 = k1 = kap` and
`p = q = 1 / kap`, so this contains the balanced case, the heavy case and the
sharp case, and it is strictly larger than all three: the dust fractions buy
inside boost quotients below the sharp threshold. -/
theorem kFourStarACell_fires_of_wall_jointCondition (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s k0 k1 p q : ℝ}
    (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hz2 : 0 < z 2) (hs : 0 < s)
    (hm0 : point.mass 0 = s * (z 0 * z 1))
    (hm1 : point.mass 1 = s * (z 0 * z 2))
    (hm2 : point.mass 2 = s * (z 1 * z 2))
    (hd3 : point.mass 3 * (1 - point.weight 3)
      = s * (z 0 * (z 0 + z 1 + z 2)) * point.weight 3)
    (hm4 : point.mass 4 = s * (z 1 * ((z 0 + z 1 + z 2) * p)))
    (hm5 : point.mass 5 = s * (z 2 * ((z 0 + z 1 + z 2) * q)))
    (hw0 : point.weight 0 * (k0 + 1) ≤ 1) (hw1 : point.weight 1 * (k1 + 1) ≤ 1)
    (hcorner : 0 < k0 * z 0 - z 2 - (z 0 + z 1 + z 2) * p)
    (hgap : z 1 * z 2 < (k0 * z 0 - z 2 - (z 0 + z 1 + z 2) * p)
      * (k1 * z 0 - z 1 - (z 0 + z 1 + z 2) * q))
    (hjoint : (z 0 + z 1 + z 2)
        * (z 2 * q ^ 2 * (k0 * z 0 - z 2 - (z 0 + z 1 + z 2) * p)
          + z 1 * p ^ 2 * (k1 * z 0 - z 1 - (z 0 + z 1 + z 2) * q)
          + 2 * (z 1 * z 2) * (p * q))
      < (z 0 - z 1 * p - z 2 * q)
        * ((k0 * z 0 - z 2 - (z 0 + z 1 + z 2) * p)
            * (k1 * z 0 - z 1 - (z 0 + z 1 + z 2) * q) - z 1 * z 2)) :
    KFourUnsignedStarACellFires point := by
  have hw0pos := point.weight_pos 0
  have hw1pos := point.weight_pos 1
  have hS : (0:ℝ) < z 0 + z 1 + z 2 := by linarith
  set al := k0 * z 0 - z 2 - (z 0 + z 1 + z 2) * p with hal
  set be := k1 * z 0 - z 1 - (z 0 + z 1 + z 2) * q with hbe
  set ga := z 0 - z 1 * p - z 2 * q with hga
  refine ⟨k0 * (s * (z 0 * z 1)), k1 * (s * (z 0 * z 2)),
    s * (z 0 * (z 0 + z 1 + z 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm0]; nlinarith [mul_pos hs (mul_pos hz0 hz1), hw0pos]
  · rw [hm1]; nlinarith [mul_pos hs (mul_pos hz0 hz2), hw1pos]
  · rw [hd3]
  · -- the corner reads `s * z 1 * al`
    have hrw : k0 * (s * (z 0 * z 1)) - (point.mass 2 + point.mass 4) = s * (z 1 * al) := by
      rw [hm2, hm4, hal]; ring
    rw [hrw]; positivity
  · have hrwX : k0 * (s * (z 0 * z 1)) - (point.mass 2 + point.mass 4) = s * (z 1 * al) := by
      rw [hm2, hm4, hal]; ring
    have hrwY : k1 * (s * (z 0 * z 2)) - (point.mass 2 + point.mass 5) = s * (z 2 * be) := by
      rw [hm2, hm5, hbe]; ring
    have hrwm : point.mass 2 = s * (z 1 * z 2) := hm2
    rw [hrwX, hrwY, hrwm]
    exact starWall_joint_minorTwo hz1 hz2 hs hgap
  · have hrwX : k0 * (s * (z 0 * z 1)) - (point.mass 2 + point.mass 4) = s * (z 1 * al) := by
      rw [hm2, hm4, hal]; ring
    have hrwY : k1 * (s * (z 0 * z 2)) - (point.mass 2 + point.mass 5) = s * (z 2 * be) := by
      rw [hm2, hm5, hbe]; ring
    have hrwZ : s * (z 0 * (z 0 + z 1 + z 2)) - (point.mass 4 + point.mass 5)
        = s * ((z 0 + z 1 + z 2) * ga) := by
      rw [hm4, hm5, hga]; ring
    have hrwm4 : point.mass 4 = s * (z 1 * ((z 0 + z 1 + z 2) * p)) := hm4
    have hrwm5 : point.mass 5 = s * (z 2 * ((z 0 + z 1 + z 2) * q)) := hm5
    rw [hrwX, hrwY, hrwZ, hm2, hrwm4, hrwm5]
    exact starWall_joint_det (a := z 0) hz1 hz2 hs hS hjoint

/-- The joint wall condition fires the full minor atlas. -/
theorem kFourAtlas_fires_of_wall_jointCondition (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s k0 k1 p q : ℝ}
    (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hz2 : 0 < z 2) (hs : 0 < s)
    (hm0 : point.mass 0 = s * (z 0 * z 1))
    (hm1 : point.mass 1 = s * (z 0 * z 2))
    (hm2 : point.mass 2 = s * (z 1 * z 2))
    (hd3 : point.mass 3 * (1 - point.weight 3)
      = s * (z 0 * (z 0 + z 1 + z 2)) * point.weight 3)
    (hm4 : point.mass 4 = s * (z 1 * ((z 0 + z 1 + z 2) * p)))
    (hm5 : point.mass 5 = s * (z 2 * ((z 0 + z 1 + z 2) * q)))
    (hw0 : point.weight 0 * (k0 + 1) ≤ 1) (hw1 : point.weight 1 * (k1 + 1) ≤ 1)
    (hcorner : 0 < k0 * z 0 - z 2 - (z 0 + z 1 + z 2) * p)
    (hgap : z 1 * z 2 < (k0 * z 0 - z 2 - (z 0 + z 1 + z 2) * p)
      * (k1 * z 0 - z 1 - (z 0 + z 1 + z 2) * q))
    (hjoint : (z 0 + z 1 + z 2)
        * (z 2 * q ^ 2 * (k0 * z 0 - z 2 - (z 0 + z 1 + z 2) * p)
          + z 1 * p ^ 2 * (k1 * z 0 - z 1 - (z 0 + z 1 + z 2) * q)
          + 2 * (z 1 * z 2) * (p * q))
      < (z 0 - z 1 * p - z 2 * q)
        * ((k0 * z 0 - z 2 - (z 0 + z 1 + z 2) * p)
            * (k1 * z 0 - z 1 - (z 0 + z 1 + z 2) * q) - z 1 * z 2)) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inl
    (kFourStarACell_fires_of_wall_jointCondition point hz0 hz1 hz2 hs hm0 hm1 hm2
      hd3 hm4 hm5 hw0 hw1 hcorner hgap hjoint)))))

/-! ## 3. The dust fraction of a capped outside weight -/

/-- The pinned outside floor turns a weight cap into a dust fraction.  If the
weight of label `4` is at most `1 / (r + 1)` then its mass cuts a fraction at
most `1 / r` out of the pinned floor. -/
theorem wall_dust_of_weight_cap (point : DirectionChartPoint 6) (label : Fin 6)
    {s v S r : ℝ} (_hr : 0 < r)
    (hd : point.mass label * (1 - point.weight label) = s * (v * S) * point.weight label)
    (hw : point.weight label * (r + 1) ≤ 1) :
    ∃ p : ℝ, 0 ≤ p ∧ p * r ≤ 1 ∧ point.mass label = s * (v * (S * p)) := by
  have hlt := directionChartPoint_weight_lt_one point label
  have hpos := point.weight_pos label
  have hone : (0:ℝ) < 1 - point.weight label := by linarith
  refine ⟨point.weight label / (1 - point.weight label), by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_le_one hone]
    nlinarith [hw, hpos]
  · have hne : (1 - point.weight label) ≠ 0 := ne_of_gt hone
    field_simp
    linear_combination hd

/-! ## 4. Two named instances strictly outside the sharp box -/

/-- **THE QUARTER AND THE EIGHTH.**  The inside weights `0` and `1` may reach
`1 / 4`, which is above the sharp box cap `(3 - √3) / 6`, once the outside
weights `4` and `5` are at most `1 / 8`. -/
theorem kFourAtlas_fires_of_wall_quarterEighth (point : DirectionChartPoint 6)
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
    (hw0 : 4 * point.weight 0 ≤ 1) (hw1 : 4 * point.weight 1 ≤ 1)
    (hw4 : 8 * point.weight 4 ≤ 1) (hw5 : 8 * point.weight 5 ≤ 1) :
    KFourAllTreeMinorAtlasCellFires point := by
  obtain ⟨p, hp0, hp7, hmp⟩ :=
    wall_dust_of_weight_cap point 4 (r := 7) (by norm_num) hd4 (by linarith)
  obtain ⟨q, hq0, hq7, hmq⟩ :=
    wall_dust_of_weight_cap point 5 (r := 7) (by norm_num) hd5 (by linarith)
  have hp : p ≤ 1 / 7 := by linarith
  have hq : q ≤ 1 / 7 := by linarith
  have hS : (0:ℝ) < z 0 + z 1 + z 2 := by linarith
  have hSle : z 0 + z 1 + z 2 ≤ 3 * z 0 := by linarith
  -- the two inside gaps and the outside gap, bounded below by the axis maximum
  have hal : 7 * (3 * z 0 - z 2 - (z 0 + z 1 + z 2) * p) ≥ 11 * z 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hSle hp0, hp, hz0]
  have hbe : 7 * (3 * z 0 - z 1 - (z 0 + z 1 + z 2) * q) ≥ 11 * z 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hSle hq0, hq, hz0]
  have hga : 7 * (z 0 - z 1 * p - z 2 * q) ≥ 5 * z 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hmax1 hp0, mul_le_mul_of_nonneg_right hmax2 hq0]
  set al := 3 * z 0 - z 2 - (z 0 + z 1 + z 2) * p with halE
  set be := 3 * z 0 - z 1 - (z 0 + z 1 + z 2) * q with hbeE
  set ga := z 0 - z 1 * p - z 2 * q with hgaE
  have halp : 0 < al := by linarith
  have hbep : 0 < be := by linarith
  have hgap : 0 < ga := by linarith
  have hbc : z 1 * z 2 ≤ z 0 * z 0 := mul_le_mul hmax1 hmax2 hz2.le hz0.le
  have hgapc : z 1 * z 2 < al * be :=
    starWall_joint_gap_of_bounds hz0 (L := 11 / 7) (by norm_num)
      (by linarith) (by linarith) hbc
  refine kFourAtlas_fires_of_wall_jointCondition point (k0 := 3) (k1 := 3) (p := p) (q := q)
    hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hmp hmq (by norm_num; linarith) (by norm_num; linarith)
    halp hgapc ?_
  -- the joint inequality, from the two axis bounds and the dust cap
  have hup : (z 0 + z 1 + z 2)
      * (z 2 * q ^ 2 * al + z 1 * p ^ 2 * be + 2 * (z 1 * z 2) * (p * q))
      ≤ 3 * z 0 * (z 0 * (1 / 49) * al + z 0 * (1 / 49) * be + 2 * (z 0 * z 0) * (1 / 49)) := by
    have hq2 : q ^ 2 ≤ 1 / 49 := by nlinarith [hq, hq0]
    have hp2 : p ^ 2 ≤ 1 / 49 := by nlinarith [hp, hp0]
    have hpq : p * q ≤ 1 / 49 := by nlinarith [hp, hq, hp0, hq0]
    have h1 : z 2 * q ^ 2 * al ≤ z 0 * (1 / 49) * al :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hmax2 hq2 (sq_nonneg q) hz0.le) halp.le
    have h2 : z 1 * p ^ 2 * be ≤ z 0 * (1 / 49) * be :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hmax1 hp2 (sq_nonneg p) hz0.le) hbep.le
    have h3 : 2 * (z 1 * z 2) * (p * q) ≤ 2 * (z 0 * z 0) * (1 / 49) := by
      have hstep : (z 1 * z 2) * (p * q) ≤ (z 0 * z 0) * (1 / 49) :=
        mul_le_mul hbc hpq (mul_nonneg hp0 hq0) (by positivity)
      linarith
    have hsum : z 2 * q ^ 2 * al + z 1 * p ^ 2 * be + 2 * (z 1 * z 2) * (p * q)
        ≤ z 0 * (1 / 49) * al + z 0 * (1 / 49) * be + 2 * (z 0 * z 0) * (1 / 49) := by
      linarith
    have hnn : (0:ℝ) ≤ z 0 * (1 / 49) * al + z 0 * (1 / 49) * be + 2 * (z 0 * z 0) * (1 / 49) := by
      nlinarith [halp.le, hbep.le, hz0.le]
    nlinarith [hsum, hSle, hS.le, hnn]
  have hT : (0:ℝ) < al * be - z 1 * z 2 := by linarith
  have hkey : 3 * z 0 * (al + be + 2 * z 0) < 35 * (al * be - z 1 * z 2) :=
    starWall_joint_key_quarter hz0 (by linarith) (by linarith) hbc
  have hlow : 3 * z 0 * (z 0 * (1 / 49) * al + z 0 * (1 / 49) * be + 2 * (z 0 * z 0) * (1 / 49))
      < ga * (al * be - z 1 * z 2) := by
    have hrw : 3 * z 0 * (z 0 * (1 / 49) * al + z 0 * (1 / 49) * be + 2 * (z 0 * z 0) * (1 / 49))
        = (z 0 / 49) * (3 * z 0 * (al + be + 2 * z 0)) := by ring
    rw [hrw]
    calc (z 0 / 49) * (3 * z 0 * (al + be + 2 * z 0))
        < (z 0 / 49) * (35 * (al * be - z 1 * z 2)) :=
          mul_lt_mul_of_pos_left hkey (by positivity)
      _ = (5 * z 0 / 7) * (al * be - z 1 * z 2) := by ring
      _ ≤ ga * (al * be - z 1 * z 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hT.le
  linarith [hup, hlow]

/-- **THREE TENTHS AND THE TWENTY-FIRST.**  The inside weights `0` and `1` may
reach `3 / 10`, which is more than two fifths above the sharp box cap, once the
outside weights `4` and `5` are at most `1 / 21`. -/
theorem kFourAtlas_fires_of_wall_threeTenthTwentyFirst (point : DirectionChartPoint 6)
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
    (hw0 : 10 * point.weight 0 ≤ 3) (hw1 : 10 * point.weight 1 ≤ 3)
    (hw4 : 21 * point.weight 4 ≤ 1) (hw5 : 21 * point.weight 5 ≤ 1) :
    KFourAllTreeMinorAtlasCellFires point := by
  obtain ⟨p, hp0, hp20, hmp⟩ :=
    wall_dust_of_weight_cap point 4 (r := 20) (by norm_num) hd4 (by linarith)
  obtain ⟨q, hq0, hq20, hmq⟩ :=
    wall_dust_of_weight_cap point 5 (r := 20) (by norm_num) hd5 (by linarith)
  have hp : p ≤ 1 / 20 := by linarith
  have hq : q ≤ 1 / 20 := by linarith
  have hS : (0:ℝ) < z 0 + z 1 + z 2 := by linarith
  have hSle : z 0 + z 1 + z 2 ≤ 3 * z 0 := by linarith
  have hal : 60 * (7 / 3 * z 0 - z 2 - (z 0 + z 1 + z 2) * p) ≥ 71 * z 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hSle hp0, hp, hz0]
  have hbe : 60 * (7 / 3 * z 0 - z 1 - (z 0 + z 1 + z 2) * q) ≥ 71 * z 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hSle hq0, hq, hz0]
  have hga : 10 * (z 0 - z 1 * p - z 2 * q) ≥ 9 * z 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hmax1 hp0, mul_le_mul_of_nonneg_right hmax2 hq0]
  set al := 7 / 3 * z 0 - z 2 - (z 0 + z 1 + z 2) * p with halE
  set be := 7 / 3 * z 0 - z 1 - (z 0 + z 1 + z 2) * q with hbeE
  set ga := z 0 - z 1 * p - z 2 * q with hgaE
  have halp : 0 < al := by linarith
  have hbep : 0 < be := by linarith
  have hgap : 0 < ga := by linarith
  have hbc : z 1 * z 2 ≤ z 0 * z 0 := mul_le_mul hmax1 hmax2 hz2.le hz0.le
  have hgapc : z 1 * z 2 < al * be :=
    starWall_joint_gap_of_bounds hz0 (L := 71 / 60) (by norm_num)
      (by linarith) (by linarith) hbc
  refine kFourAtlas_fires_of_wall_jointCondition point (k0 := 7 / 3) (k1 := 7 / 3)
    (p := p) (q := q) hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hmp hmq
    (by norm_num; linarith) (by norm_num; linarith) halp hgapc ?_
  have hup : (z 0 + z 1 + z 2)
      * (z 2 * q ^ 2 * al + z 1 * p ^ 2 * be + 2 * (z 1 * z 2) * (p * q))
      ≤ 3 * z 0 * (z 0 * (1 / 400) * al + z 0 * (1 / 400) * be
        + 2 * (z 0 * z 0) * (1 / 400)) := by
    have hq2 : q ^ 2 ≤ 1 / 400 := by nlinarith [hq, hq0]
    have hp2 : p ^ 2 ≤ 1 / 400 := by nlinarith [hp, hp0]
    have hpq : p * q ≤ 1 / 400 := by nlinarith [hp, hq, hp0, hq0]
    have h1 : z 2 * q ^ 2 * al ≤ z 0 * (1 / 400) * al :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hmax2 hq2 (sq_nonneg q) hz0.le) halp.le
    have h2 : z 1 * p ^ 2 * be ≤ z 0 * (1 / 400) * be :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hmax1 hp2 (sq_nonneg p) hz0.le) hbep.le
    have h3 : 2 * (z 1 * z 2) * (p * q) ≤ 2 * (z 0 * z 0) * (1 / 400) := by
      have hstep : (z 1 * z 2) * (p * q) ≤ (z 0 * z 0) * (1 / 400) :=
        mul_le_mul hbc hpq (mul_nonneg hp0 hq0) (by positivity)
      linarith
    have hsum : z 2 * q ^ 2 * al + z 1 * p ^ 2 * be + 2 * (z 1 * z 2) * (p * q)
        ≤ z 0 * (1 / 400) * al + z 0 * (1 / 400) * be + 2 * (z 0 * z 0) * (1 / 400) := by
      linarith
    have hnn : (0:ℝ) ≤ z 0 * (1 / 400) * al + z 0 * (1 / 400) * be
        + 2 * (z 0 * z 0) * (1 / 400) := by
      nlinarith [halp.le, hbep.le, hz0.le]
    nlinarith [hsum, hSle, hS.le, hnn]
  have hT : (0:ℝ) < al * be - z 1 * z 2 := by linarith
  have hkey : z 0 * (al + be + 2 * z 0) < 120 * (al * be - z 1 * z 2) :=
    starWall_joint_key_threeTenth hz0 (by linarith) (by linarith) hbc
  have hlow : 3 * z 0 * (z 0 * (1 / 400) * al + z 0 * (1 / 400) * be
        + 2 * (z 0 * z 0) * (1 / 400))
      < ga * (al * be - z 1 * z 2) := by
    have hrw : 3 * z 0 * (z 0 * (1 / 400) * al + z 0 * (1 / 400) * be
          + 2 * (z 0 * z 0) * (1 / 400))
        = (3 * z 0 / 400) * (z 0 * (al + be + 2 * z 0)) := by ring
    rw [hrw]
    calc (3 * z 0 / 400) * (z 0 * (al + be + 2 * z 0))
        < (3 * z 0 / 400) * (120 * (al * be - z 1 * z 2)) :=
          mul_lt_mul_of_pos_left hkey (by positivity)
      _ = (9 * z 0 / 10) * (al * be - z 1 * z 2) := by ring
      _ ≤ ga * (al * be - z 1 * z 2) :=
          mul_le_mul_of_nonneg_right (by linarith) hT.le
  have hgoal : (z 0 + z 1 + z 2)
        * (z 2 * q ^ 2 * al + z 1 * p ^ 2 * be + 2 * (z 1 * z 2) * (p * q))
      < ga * (al * be - z 1 * z 2) := by linarith [hup, hlow]
  exact hgoal

end Gtz
