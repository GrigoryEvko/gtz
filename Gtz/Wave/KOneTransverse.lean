import Gtz.Wave.KOneNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The transverse axis of the one-zero stratum

The normal form put the live pair in two coordinates.  This module supplies
the THIRD axis and closes the ledger on it, at general size `m`.

The live pair spans a plane containing the null direction, so its cross
product `nu = g_y x g_z` is the axis transverse to that plane.  Three facts
make it the right coordinate and all three are exact:

* `Gtz.pairAnchor_cross_normSq` — `|nu|^2 = l_y + l_z - 1 = A`, the WEDGE.
  The transverse axis is scaled by the very quantity the collision is fought
  on.
* `Gtz.pairAnchor_cross_dot_null` — `nu . w = 0`: the axis is orthogonal to
  the null direction, because the null direction lies in the pair's plane.
* `Gtz.cross_dot_erased_eq_bracket` — the erased atom reads the axis by the
  BRACKET: `g_x . nu = [x y z]`.  So the stratum's bracket is literally its
  transverse reading.

Three consequences, each new and each weight-carrying:

* **`Gtz.kOne_bracket_gt_wedge`** — `[xyz]^2 > l_y + l_z - 1`, STRICTLY.  The
  gap form is strictly positive off the null line, the axis is off it, and
  the gap form at the axis is exactly `[xyz]^2 - A`.  Frame-free: no
  orthonormal basis is ever built.
* **`Gtz.kOne_transverse_parseval`** — THE TRANSVERSE LEDGER:

    `t_x·[xyz]^2 + Σ_{d ∉ C} t_d·(q_d . nu)^2 = l_y + l_z - 1` .

  The erased atom's bracket and the outside readings split the wedge
  EXACTLY.  Parseval read on the transverse axis, with the live pair
  contributing nothing because it is orthogonal to its own cross product.
* **`Gtz.kOne_erased_weight_cap`** — `t_x·[xyz]^2 ≤ l_y + l_z - 1`, the first
  cap on the ERASED weight, which every previous law of the stratum left
  free.  With the strict bracket floor it forces `t_x < 1` and, sharply,
  `t_x ≤ A/[xyz]^2`.

Together with the strict wedge floor `A > 1` and the sharp live cap
`A·(t_y·beta_z^2 + t_z·beta_y^2) ≤ 1`, the stratum's collision now binds all
three weights: the live pair from `Gtz.kOne_sharp_weight_cap`, the erased
atom from here, and the outside through the transverse ledger's remainder.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The transverse axis of an anchored pair -/

/-- A cross product is orthogonal to its left factor. -/
theorem cross_dot_left (u v : Fin 3 → ℝ) : u ⬝ᵥ crossProduct u v = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- A cross product is orthogonal to its right factor. -/
theorem cross_dot_right (u v : Fin 3 → ℝ) : v ⬝ᵥ crossProduct u v = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The bracket is invariant under the cyclic shift of its arguments. -/
theorem tripleBracket_cyclic (u v g : Fin 3 → ℝ) :
    tripleBracket g u v = tripleBracket u v g := by
  simp only [tripleBracket_eq]
  ring

/-- **THE ERASED ATOM READS THE AXIS BY THE BRACKET.** -/
theorem cross_dot_erased_eq_bracket (gy gz g : Fin 3 → ℝ) :
    g ⬝ᵥ crossProduct gy gz = tripleBracket g gy gz := by
  rw [tripleBracket_cyclic, tripleBracket_eq_cross_dot, dotProduct_comm]

/-- **THE AXIS IS SCALED BY THE WEDGE.**  At an anchored pair the squared
length of the cross product is exactly `l_y + l_z - 1`. -/
theorem pairAnchor_cross_normSq {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    crossProduct gy gz ⬝ᵥ crossProduct gy gz
      = leverageOf gy + leverageOf gz - 1 := by
  rw [cross_dotProduct_self, ← leverageOf_eq_dotProduct,
    ← leverageOf_eq_dotProduct]
  exact pairAnchor_wedge_value hanchor hunit

/-- **THE AXIS IS ORTHOGONAL TO THE NULL DIRECTION**, because the null
direction lies in the pair's own plane. -/
theorem pairAnchor_cross_dot_null {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w) :
    w ⬝ᵥ crossProduct gy gz = 0 := by
  have hres := pairAnchor_resolve hanchor
  rw [← hres, add_dotProduct, smul_dotProduct, smul_dotProduct,
    cross_dot_left, cross_dot_right]
  simp

/-- The axis is nonzero once the pair carries wedge above one. -/
theorem pairAnchor_cross_ne_zero {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1)
    (hA : 1 < leverageOf gy + leverageOf gz - 1) :
    crossProduct gy gz ≠ 0 := by
  intro hzero
  have hnorm := pairAnchor_cross_normSq hanchor hunit
  rw [hzero] at hnorm
  simp only [zero_dotProduct] at hnorm
  linarith [hA, hnorm]

/-! ## 2. The strict bracket floor -/

variable {m : ℕ}

/-- The gap form of a triple, expanded at a probe. -/
theorem kOne_tripleGap_form (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin m)) - 1) *ᵥ probe)
      = (D.atom x ⬝ᵥ probe) ^ 2 + (D.atom y ⬝ᵥ probe) ^ 2
        + (D.atom z ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe := by
  classical
  have hsum : subsetSum D ({x, y, z} : Finset (Fin m))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hsum,
    Matrix.add_mulVec, Matrix.add_mulVec,
    show atomMatrix (D.atom x) *ᵥ probe = (D.atom x ⬝ᵥ probe) • D.atom x from
      vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom y) *ᵥ probe = (D.atom y ⬝ᵥ probe) • D.atom y from
      vecMulVec_mulVec_eq _ _ _,
    show atomMatrix (D.atom z) *ᵥ probe = (D.atom z ⬝ᵥ probe) • D.atom z from
      vecMulVec_mulVec_eq _ _ _,
    dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
    dotProduct_smul]
  simp only [smul_eq_mul, dotProduct_comm probe (D.atom x),
    dotProduct_comm probe (D.atom y), dotProduct_comm probe (D.atom z)]
  ring

/-- **THE STRICT BRACKET FLOOR OF THE STRATUM.**  At a `K1` corank-one
dominator the squared bracket STRICTLY exceeds the live wedge:

  `[x y z]^2 > l_y + l_z - 1` .

The transverse axis is off the null line (it is orthogonal to it and
nonzero), so the gap form there is strictly positive; and the gap form at
the axis is exactly `[xyz]^2 - (l_y + l_z - 1)`, because the live pair is
orthogonal to its own cross product while the axis has squared length the
wedge.  Frame-free — no orthonormal basis is ever constructed. -/
theorem kOne_bracket_gt_wedge (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) w)
    (hunit : w ⬝ᵥ w = 1)
    (hanchor : (atomMatrix (D.atom y) + atomMatrix (D.atom z)) *ᵥ w = w)
    (hA : 1 < leverageOf (D.atom y) + leverageOf (D.atom z) - 1) :
    leverageOf (D.atom y) + leverageOf (D.atom z) - 1
      < atomBracket D x y z ^ 2 := by
  classical
  set nu : Fin 3 → ℝ := crossProduct (D.atom y) (D.atom z) with hnu
  have hnn : nu ⬝ᵥ nu = leverageOf (D.atom y) + leverageOf (D.atom z) - 1 :=
    pairAnchor_cross_normSq hanchor hunit
  have hyn : D.atom y ⬝ᵥ nu = 0 := cross_dot_left _ _
  have hzn : D.atom z ⬝ᵥ nu = 0 := cross_dot_right _ _
  have hxn : D.atom x ⬝ᵥ nu = atomBracket D x y z := by
    rw [hnu, cross_dot_erased_eq_bracket, atomBracket]
  have hwn : w ⬝ᵥ nu = 0 := pairAnchor_cross_dot_null hanchor
  -- the axis is off the null line
  have hoff : ∀ scale : ℝ, nu ≠ scale • w := by
    intro scale hcon
    have hnw : nu ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact hwn
    rw [hcon, smul_dotProduct, hunit, smul_eq_mul, mul_one] at hnw
    rw [hcon, hnw, zero_smul] at hnn
    simp only [zero_dotProduct] at hnn
    linarith [hA, hnn]
  have hpos := gapForm_pos_of_gapNullLine D _ hline hdominates hoff
  rw [kOne_tripleGap_form D hxy hxz hyz nu, hxn, hyn, hzn, hnn] at hpos
  linarith [hpos]

/-! ## 3. The transverse ledger -/

/-- **THE TRANSVERSE LEDGER.**  Parseval read on the transverse axis: the
erased atom's squared bracket and the outside readings split the wedge
EXACTLY,

  `t_x·[xyz]^2 + Σ_{d ∉ C} t_d·(q_d . nu)^2 = l_y + l_z - 1` ,

with `nu = g_y x g_z`.  The live pair contributes nothing, being orthogonal
to its own cross product. -/
theorem kOne_transverse_parseval (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {w : Fin 3 → ℝ} (hunit : w ⬝ᵥ w = 1)
    (hanchor : (atomMatrix (D.atom y) + atomMatrix (D.atom z)) *ᵥ w = w) :
    D.weight x * atomBracket D x y z ^ 2
        + ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
            D.weight d * (D.atom d ⬝ᵥ crossProduct (D.atom y) (D.atom z)) ^ 2
      = leverageOf (D.atom y) + leverageOf (D.atom z) - 1 := by
  classical
  set nu : Fin 3 → ℝ := crossProduct (D.atom y) (D.atom z) with hnu
  have hpar := parseval_probe_form D nu
  rw [pairAnchor_cross_normSq hanchor hunit] at hpar
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin m))
    (fun c => D.weight c * (D.atom c ⬝ᵥ nu) ^ 2)
  rw [hpar, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton] at hsplit
  have hyn : D.atom y ⬝ᵥ nu = 0 := cross_dot_left _ _
  have hzn : D.atom z ⬝ᵥ nu = 0 := cross_dot_right _ _
  have hxn : D.atom x ⬝ᵥ nu = atomBracket D x y z := by
    rw [hnu, cross_dot_erased_eq_bracket, atomBracket]
  rw [hyn, hzn, hxn] at hsplit
  linear_combination hsplit

/-- **THE ERASED WEIGHT CAP.**  The first cap on the erased weight, which
every earlier law of the stratum left free:

  `t_x·[xyz]^2 ≤ l_y + l_z - 1` .

The outside readings of the transverse axis are the slack. -/
theorem kOne_erased_weight_cap (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {w : Fin 3 → ℝ} (hunit : w ⬝ᵥ w = 1)
    (hanchor : (atomMatrix (D.atom y) + atomMatrix (D.atom z)) *ᵥ w = w) :
    D.weight x * atomBracket D x y z ^ 2
      ≤ leverageOf (D.atom y) + leverageOf (D.atom z) - 1 := by
  classical
  have hled := kOne_transverse_parseval D hxy hxz hyz hunit hanchor
  have hrest : 0 ≤ ∑ d ∈ (({x, y, z} : Finset (Fin m))ᶜ),
      D.weight d * (D.atom d ⬝ᵥ crossProduct (D.atom y) (D.atom z)) ^ 2 :=
    Finset.sum_nonneg fun d _ => mul_nonneg (D.weight_pos d).le (sq_nonneg _)
  linarith [hled, hrest]

/-- **THE ERASED WEIGHT IS STRICTLY SUBUNIT ON THE STRATUM.**  The strict
bracket floor turns the erased cap into `t_x < 1` with room to spare: the
erased weight is at most the wedge over the squared bracket, a ratio the
floor keeps strictly below one. -/
theorem kOne_erased_weight_lt_one (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin m)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin m)) w)
    (hunit : w ⬝ᵥ w = 1)
    (hanchor : (atomMatrix (D.atom y) + atomMatrix (D.atom z)) *ᵥ w = w)
    (hA : 1 < leverageOf (D.atom y) + leverageOf (D.atom z) - 1) :
    D.weight x < 1 := by
  have hcap := kOne_erased_weight_cap D hxy hxz hyz hunit hanchor
  have hgt := kOne_bracket_gt_wedge D hxy hxz hyz hdominates hline hunit
    hanchor hA
  nlinarith [hcap, hgt, D.weight_pos x, hA]

/-! ## 4. The stratum forms of the transverse laws -/

/-- The strict bracket floor at a `K1` dominator, with the anchor and the
wedge floor supplied by the stratum. -/
theorem kOne_bracket_gt_wedge_of_null (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (hbz : D.atom z ⬝ᵥ w ≠ 0) :
    leverageOf (D.atom y) + leverageOf (D.atom z) - 1
      < atomBracket D x y z ^ 2 := by
  have hstrict := kOne_two_lt_leverageSum D hxy hxz hyz hdominates hline hunit
    hax hbz
  exact kOne_bracket_gt_wedge D hxy hxz hyz hdominates hline hunit
    (kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax) (by linarith)

/-- The erased weight cap at a `K1` dominator. -/
theorem kOne_erased_weight_cap_of_null (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0) :
    D.weight x * atomBracket D x y z ^ 2
      ≤ leverageOf (D.atom y) + leverageOf (D.atom z) - 1 :=
  kOne_erased_weight_cap D hxy hxz hyz hunit
    (kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax)

/-- **THE THREE-WEIGHT COLLISION OF THE STRATUM.**  Every weight of a `K1`
dominator is now capped against the same wedge `A = l_y + l_z - 1`:

  `A > 1` ,     `A·(t_y·beta_z^2 + t_z·beta_y^2) ≤ 1` ,     `t_x·A < A` ,

the last through the strict bracket floor.  The live pair, the erased atom
and (through the ledger's remainder) the outside all pay on one quantity. -/
theorem kOne_three_weight_collision (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (hbz : D.atom z ⬝ᵥ w ≠ 0) :
    1 < leverageOf (D.atom y) + leverageOf (D.atom z) - 1
      ∧ (leverageOf (D.atom y) + leverageOf (D.atom z) - 1)
          * (D.weight y * (D.atom z ⬝ᵥ w) ^ 2
            + D.weight z * (D.atom y ⬝ᵥ w) ^ 2) ≤ 1
      ∧ D.weight x * atomBracket D x y z ^ 2
          ≤ leverageOf (D.atom y) + leverageOf (D.atom z) - 1
      ∧ leverageOf (D.atom y) + leverageOf (D.atom z) - 1
          < atomBracket D x y z ^ 2 := by
  refine ⟨?_, kOne_sharp_weight_cap_of_null D hxy hxz hyz hdominates hline
      hunit hax hbz,
    kOne_erased_weight_cap_of_null D hxy hxz hyz hdominates hline hunit hax,
    kOne_bracket_gt_wedge_of_null D hxy hxz hyz hdominates hline hunit hax hbz⟩
  have := kOne_two_lt_leverageSum D hxy hxz hyz hdominates hline hunit hax hbz
  linarith

end Gtz
