import Gtz.Wave.KOneAnchor
import Gtz.Wave.PairBracketMass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The bracket ledger of the one-zero stratum

The anchor module reduced `K1` to sixteen refusals and priced its live pair
by two opposing laws.  This module lands the currency layer on top: the
bracket of a `K1` dominator is an exact polynomial in leverages and
pairings, the stratum's wedge floor is STRICT, and every genuine `K1`
dominator forces a strictly refused triple through its live pair.

The general laws (any design, any triple):

* `Gtz.det_shift_one` — `det(G + 1) = 1 + tr G + e2(G) + det G`: the
  characteristic expansion of a unit shift.
* `Gtz.det_tripleSum_eq_bracket_sq` — `det(S_T) = [T]^2`: Cauchy–Binet at a
  square block, with no compound matrices.
* `Gtz.dominator_bracket_floor` — **EVERY weak dominator has `[C]^2 >= 1`**:
  the shift expansion reads the squared bracket as one plus the three gap
  invariants, and positive semidefiniteness signs all three.  Against the
  bracket budget — the twenty weighted squared brackets total one — a
  dominator alone consumes the share `t_x t_y t_z` of the whole design.
* `Gtz.corankOne_bracket_sq_eq` — at a singular gap the floor is exact:
  `[C]^2 = 1 + tr(S_C - 1) + e2(S_C - 1)`.

The `K1` laws (at an anchored pair, then at the dominator):

* `Gtz.pairAnchor_transverse_split` — THE TRANSVERSE SPLIT: the transverse
  mass of each live atom is the OPPOSITE reading squared times the wedge,
  `l_y - beta_y^2 = (l_y + l_z - 1)·beta_z^2`.
* `Gtz.pairAnchor_bracket_mirror` / `Gtz.pairAnchor_bracket_master` — THE
  MASTER BRACKET LAW: with the third atom orthogonal to the null direction,
  `[xyz]^2 = (l_y + l_z - 1)·l_x - <g_x,g_y>^2 - <g_x,g_z>^2`.  The bracket
  of the stratum is the wedge times the erased leverage minus the two cross
  pairings — the tax currencies, with no residue.
* `Gtz.kOne_two_lt_leverageSum` — THE STRICT WEDGE FLOOR: a GENUINE `K1`
  dominator (gap corank exactly one) carries `l_y + l_z > 2` STRICTLY.  At
  equality the live pair would be orthonormal, the erased atom orthogonal to
  it, and the transverse part of `g_y` a second null line.
* `Gtz.kOne_transverse_pos` / `Gtz.kOne_pair_weight_cap_of_null` — the
  transverse mass of each live atom is strictly positive, so the Parseval
  weight cap of the anchor module holds UNCONDITIONALLY on the stratum:
  `min(t_y, t_z)·(l_y + l_z - 1) <= 1`.
* `Gtz.kOne_bracket_weight_cap` — the two caps meet in the bracket:
  `min(t_y, t_z)·[xyz]^2 <= l_x`.
* `Gtz.kOne_outside_null_mass` — the outside null mass is exact:
  `Σ_{d ∉ C} t_d·(q_d.w)^2 = 1 - t_y·beta_y^2 - t_z·beta_z^2`.
* `Gtz.kOne_exists_strict_refusal` — a genuine `K1` dominator forces an
  outside atom that reads the null direction, and its live-pair triple is
  refused with STRICTLY NEGATIVE gap determinant.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The shift expansion and the bracket floor -/

/-- **THE UNIT-SHIFT EXPANSION.**  For every `3×3` matrix,
`det(G + 1) = 1 + tr G + e2(G) + det G` — the characteristic polynomial of
`G` read at `-1`. -/
theorem det_shift_one (G : Matrix (Fin 3) (Fin 3) ℝ) :
    (G + 1).det
      = 1 + Matrix.trace G
        + ((Matrix.trace G) ^ 2 - Matrix.trace (G * G)) / 2
        + G.det := by
  simp only [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.mul_apply,
    Matrix.add_apply, Matrix.one_apply, Fin.sum_univ_three]
  norm_num [Fin.ext_iff]
  ring

/-- **CAUCHY–BINET AT A SQUARE BLOCK.**  The determinant of a three-atom
sum is the squared bracket, with no compound matrices. -/
theorem det_tripleSum_eq_bracket_sq (a b c : Fin 3 → ℝ) :
    (atomMatrix a + atomMatrix b + atomMatrix c).det
      = tripleBracket a b c ^ 2 := by
  simp only [Matrix.det_fin_three, Matrix.add_apply, atomMatrix,
    Matrix.vecMulVec_apply, tripleBracket_eq]
  ring

/-- The trace of a positive semidefinite `3×3` matrix is nonnegative. -/
theorem posSemidef_trace_nonneg {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hG : G.PosSemidef) : 0 ≤ Matrix.trace G := by
  have hdiag : ∀ i : Fin 3, 0 ≤ G i i := by
    intro i
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hG).2 (Pi.single i 1)
    rw [star_trivial, Matrix.mulVec_single_one, single_one_dotProduct] at h
    simpa using h
  rw [Matrix.trace_fin_three]
  have h0 := hdiag 0
  have h1 := hdiag 1
  have h2 := hdiag 2
  linarith

/-- **THE BRACKET FLOOR OF A WEAK DOMINATOR.**  A weakly dominating triple
has squared bracket at least one: the shift expansion reads `[C]^2` as one
plus the three invariants of the gap, and positive semidefiniteness signs
every invariant.  Against the bracket budget, a dominator alone consumes the
share `t_x t_y t_z` of the design's whole unit of weighted bracket mass. -/
theorem dominator_bracket_floor (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6))) :
    1 ≤ atomBracket D x y z ^ 2 := by
  classical
  have hsum : subsetSum D ({x, y, z} : Finset (Fin 6))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  have hdetbr : (subsetSum D ({x, y, z} : Finset (Fin 6))).det
      = tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 := by
    rw [hsum, det_tripleSum_eq_bracket_sq]
  have hshift := det_shift_one (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
  have hone : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 + 1
      = subsetSum D ({x, y, z} : Finset (Fin 6)) := by abel
  rw [hone, hdetbr] at hshift
  have htr := posSemidef_trace_nonneg hdominates
  have he2 := e2_nonneg_of_posSemidef hdominates
  have hdet := Matrix.PosSemidef.det_nonneg hdominates
  rw [atomBracket]
  linarith [hshift, htr, he2, hdet]

/-- The bracket floor with the gap trace kept: `1 + tr(S_C - 1) <= [C]^2`. -/
theorem dominator_bracket_floor_add_trace (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6))) :
    1 + Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
      ≤ atomBracket D x y z ^ 2 := by
  classical
  have hsum : subsetSum D ({x, y, z} : Finset (Fin 6))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  have hdetbr : (subsetSum D ({x, y, z} : Finset (Fin 6))).det
      = tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 := by
    rw [hsum, det_tripleSum_eq_bracket_sq]
  have hshift := det_shift_one (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
  have hone : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 + 1
      = subsetSum D ({x, y, z} : Finset (Fin 6)) := by abel
  rw [hone, hdetbr] at hshift
  have he2 := e2_nonneg_of_posSemidef hdominates
  have hdet := Matrix.PosSemidef.det_nonneg hdominates
  rw [atomBracket]
  linarith [hshift, he2, hdet]

/-- **THE SINGULAR-GAP BRACKET VALUE.**  When the gap of a weak dominator is
singular — every corank-one dominator in particular — the floor is exact:
`[C]^2 = 1 + tr(S_C - 1) + e2(S_C - 1)`. -/
theorem corankOne_bracket_sq_eq (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hw : w ≠ 0)
    (hnull : w ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 6)) - 1) *ᵥ w) = 0) :
    atomBracket D x y z ^ 2
      = 1 + Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
        + ((Matrix.trace (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)) ^ 2
            - Matrix.trace ((subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
              * (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1))) / 2 := by
  classical
  have hker : (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1) *ᵥ w = 0 :=
    mulVec_eq_zero_of_form_eq_zero hdominates
      (transpose_subsetSum_sub_one D ({x, y, z} : Finset (Fin 6))) hnull
  have hdet : (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1).det = 0 := by
    by_contra hne
    exact hw (Matrix.eq_zero_of_mulVec_eq_zero hne hker)
  have hsum : subsetSum D ({x, y, z} : Finset (Fin 6))
      = atomMatrix (D.atom x) + atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  have hdetbr : (subsetSum D ({x, y, z} : Finset (Fin 6))).det
      = tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 := by
    rw [hsum, det_tripleSum_eq_bracket_sq]
  have hshift := det_shift_one (subsetSum D ({x, y, z} : Finset (Fin 6)) - 1)
  have hone : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 + 1
      = subsetSum D ({x, y, z} : Finset (Fin 6)) := by abel
  rw [hone, hdetbr, hdet] at hshift
  rw [atomBracket]
  linarith [hshift]

/-! ## 2. The transverse split and the master bracket law -/

/-- **THE TRANSVERSE SPLIT.**  At an anchored pair, the transverse mass of
each live atom is the OPPOSITE squared reading times the wedge:
`l_y - beta_y^2 = (l_y + l_z - 1)·beta_z^2`.  One tiny certificate:
`beta_y·h1 - beta_z·h2 - l_y·h3`. -/
theorem pairAnchor_transverse_split {gy gz w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) :
    leverageOf gy - (gy ⬝ᵥ w) ^ 2
      = (leverageOf gy + leverageOf gz - 1) * (gz ⬝ᵥ w) ^ 2 := by
  have h1 := pairAnchor_relation_left hanchor
  have h2 := pairAnchor_relation_right hanchor
  have h3 := pairAnchor_readings_sq_sum hanchor hunit
  linear_combination (gy ⬝ᵥ w) * h1 - (gz ⬝ᵥ w) * h2 - leverageOf gy * h3

/-- **THE BRACKET MIRROR.**  At an anchored pair with the third atom
orthogonal to the null direction, the squared bracket splits through either
live reading: `beta_z^2·[g,y,z]^2 = l_g·(l_y - beta_y^2) - <g,g_y>^2`. -/
theorem pairAnchor_bracket_mirror {gy gz g w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) (hax : g ⬝ᵥ w = 0) :
    (gz ⬝ᵥ w) ^ 2 * tripleBracket g gy gz ^ 2
      = leverageOf g * (leverageOf gy - (gy ⬝ᵥ w) ^ 2) - (g ⬝ᵥ gy) ^ 2 := by
  have h1 := pairAnchor_relation_left hanchor
  have h2 := pairAnchor_relation_right hanchor
  have h3 := pairAnchor_readings_sq_sum hanchor hunit
  have h4 : (gy ⬝ᵥ w) * (g ⬝ᵥ gy) + (gz ⬝ᵥ w) * (g ⬝ᵥ gz) = 0 := by
    have h : g ⬝ᵥ ((gy ⬝ᵥ w) • gy + (gz ⬝ᵥ w) • gz) = g ⬝ᵥ w := by
      rw [pairAnchor_resolve hanchor]
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hax] at h
    linear_combination h
  rw [tripleBracket_sq_gram]
  simp only [dotProduct_comm gz g]
  linear_combination
    (-((gy ⬝ᵥ w) * leverageOf g) + (gy ⬝ᵥ w) * (g ⬝ᵥ gy) ^ 2
        - (gz ⬝ᵥ w) * leverageOf g * (gy ⬝ᵥ gz)
        + 2 * (gz ⬝ᵥ w) * (g ⬝ᵥ gy) * (g ⬝ᵥ gz)) * h1
    + ((gz ⬝ᵥ w) * leverageOf g * leverageOf gy
        - (gz ⬝ᵥ w) * (g ⬝ᵥ gy) ^ 2) * h2
    + (leverageOf g * leverageOf gy - (g ⬝ᵥ gy) ^ 2) * h3
    + (-((gy ⬝ᵥ w) * leverageOf gy * (g ⬝ᵥ gy))
        + 2 * (gy ⬝ᵥ w) * (g ⬝ᵥ gy)
        - (gz ⬝ᵥ w) * leverageOf gy * (g ⬝ᵥ gz)) * h4

/-- **THE MASTER BRACKET LAW.**  At an anchored pair with the third atom
orthogonal to the null direction:

  `[g,y,z]^2 = (l_y + l_z - 1)·l_g - <g,g_y>^2 - <g,g_z>^2` .

The squared bracket IS the pair wedge times the third leverage minus the two
cross pairings: the `K1` stratum computes its own bracket exactly, in the
two currencies of the wedge-bracket tax, with no residue. -/
theorem pairAnchor_bracket_master {gy gz g w : Fin 3 → ℝ}
    (hanchor : (atomMatrix gy + atomMatrix gz) *ᵥ w = w)
    (hunit : w ⬝ᵥ w = 1) (hax : g ⬝ᵥ w = 0) :
    tripleBracket g gy gz ^ 2
      = (leverageOf gy + leverageOf gz - 1) * leverageOf g
        - (g ⬝ᵥ gy) ^ 2 - (g ⬝ᵥ gz) ^ 2 := by
  have hanchor' : (atomMatrix gz + atomMatrix gy) *ᵥ w = w := by
    rwa [add_comm (atomMatrix gz)]
  have hmirY := pairAnchor_bracket_mirror hanchor hunit hax
  have hmirZ := pairAnchor_bracket_mirror hanchor' hunit hax
  have h3 := pairAnchor_readings_sq_sum hanchor hunit
  have hswap : tripleBracket g gz gy ^ 2 = tripleBracket g gy gz ^ 2 := by
    simp only [tripleBracket_eq]
    ring
  rw [hswap] at hmirZ
  linear_combination hmirY + hmirZ
    - (tripleBracket g gy gz ^ 2 + leverageOf g) * h3

/-! ## 3. The strict wedge floor of the genuine stratum -/

/-- **THE STRICT WEDGE FLOOR.**  A GENUINE `K1` dominator — gap corank
exactly one, both live readings nonzero — carries `2 < l_y + l_z` STRICTLY.
At equality the live pair would be orthonormal and the erased atom
orthogonal to it, and the transverse part of `g_y` would be a second null
direction off the null line. -/
theorem kOne_two_lt_leverageSum (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (hbz : D.atom z ⬝ᵥ w ≠ 0) :
    2 < leverageOf (D.atom y) + leverageOf (D.atom z) := by
  classical
  rcases lt_or_eq_of_le
    (kOne_two_le_leverageSum D hxy hxz hyz hdominates hline hunit hax) with h | h
  · exact h
  exfalso
  have hanchor := kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax
  have hsplitY := pairAnchor_transverse_split hanchor hunit
  have h3 := pairAnchor_readings_sq_sum hanchor hunit
  have hsum2 : leverageOf (D.atom y) + leverageOf (D.atom z) = 2 := h.symm
  -- both live atoms are unit
  have hly : leverageOf (D.atom y) = 1 := by
    have hval : leverageOf (D.atom y) - (D.atom y ⬝ᵥ w) ^ 2
        = (D.atom z ⬝ᵥ w) ^ 2 := by
      rw [hsplitY, hsum2]; ring
    nlinarith [hval, h3]
  have hlz : leverageOf (D.atom z) = 1 := by linarith [hsum2, hly]
  have hly' : D.atom y ⬝ᵥ D.atom y = 1 := by
    rw [← leverageOf_eq_dotProduct]; exact hly
  -- the erased pairings vanish through the nonnegative second invariant
  have hsumM : subsetSum D ({x, y, z} : Finset (Fin 6))
      = atomMatrix (D.atom y) + atomMatrix (D.atom z) + atomMatrix (D.atom x) := by
    rw [subsetSum, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    abel
  have hpsd : (atomMatrix (D.atom y) + atomMatrix (D.atom z)
      + atomMatrix (D.atom x) - 1).PosSemidef := by
    rw [← hsumM]; exact hdominates
  have he2 := e2_nonneg_of_posSemidef hpsd
  rw [pairAnchor_e2_price hanchor hunit, hly, hlz] at he2
  have hpxy : D.atom x ⬝ᵥ D.atom y = 0 := by
    nlinarith [he2, sq_nonneg (D.atom x ⬝ᵥ D.atom y),
      sq_nonneg (D.atom x ⬝ᵥ D.atom z)]
  have hpzx : D.atom x ⬝ᵥ D.atom z = 0 := by
    nlinarith [he2, sq_nonneg (D.atom x ⬝ᵥ D.atom y),
      sq_nonneg (D.atom x ⬝ᵥ D.atom z)]
  -- the live pairing vanishes through the wedge value
  have hwedge := pairAnchor_wedge_value hanchor hunit
  rw [hly, hlz] at hwedge
  have hpyz : D.atom y ⬝ᵥ D.atom z = 0 := by nlinarith [hwedge]
  -- the transverse probe of the first live atom
  set v : Fin 3 → ℝ := D.atom y - (D.atom y ⬝ᵥ w) • w with hv
  have hyv : D.atom y ⬝ᵥ v = (D.atom z ⬝ᵥ w) ^ 2 := by
    rw [hv, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linear_combination hly' - h3
  have hzv : D.atom z ⬝ᵥ v = -((D.atom y ⬝ᵥ w) * (D.atom z ⬝ᵥ w)) := by
    rw [hv, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (D.atom z) (D.atom y)]
    linear_combination hpyz
  have hxv : D.atom x ⬝ᵥ v = 0 := by
    rw [hv, dotProduct_sub, dotProduct_smul, smul_eq_mul, hpxy, hax]
    ring
  have hvv : v ⬝ᵥ v = (D.atom z ⬝ᵥ w) ^ 2 := by
    rw [hv]
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hunit, mul_one]
    rw [dotProduct_comm w (D.atom y)]
    linear_combination hly' - h3
  -- the gap form vanishes at the transverse probe
  have hSCv : subsetSum D ({x, y, z} : Finset (Fin 6)) *ᵥ v
      = (D.atom y ⬝ᵥ v) • D.atom y + (D.atom z ⬝ᵥ v) • D.atom z
        + (D.atom x ⬝ᵥ v) • D.atom x := by
    rw [hsumM, Matrix.add_mulVec, Matrix.add_mulVec,
      show atomMatrix (D.atom y) *ᵥ v = (D.atom y ⬝ᵥ v) • D.atom y from
        vecMulVec_mulVec_eq _ _ _,
      show atomMatrix (D.atom z) *ᵥ v = (D.atom z ⬝ᵥ v) • D.atom z from
        vecMulVec_mulVec_eq _ _ _,
      show atomMatrix (D.atom x) *ᵥ v = (D.atom x ⬝ᵥ v) • D.atom x from
        vecMulVec_mulVec_eq _ _ _]
  have hform : v ⬝ᵥ ((subsetSum D ({x, y, z} : Finset (Fin 6)) - 1) *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, hSCv,
      dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_smul]
    simp only [smul_eq_mul, dotProduct_comm v (D.atom y),
      dotProduct_comm v (D.atom z), dotProduct_comm v (D.atom x)]
    rw [hyv, hzv, hxv, hvv]
    linear_combination (D.atom z ⬝ᵥ w) ^ 2 * h3
  -- corank one forces the probe onto the null line, which kills it
  obtain ⟨s, hs⟩ := hline.2.2 v hform
  have hvw : v ⬝ᵥ w = 0 := by
    rw [hv, sub_dotProduct, smul_dotProduct, hunit, smul_eq_mul]
    ring
  have hs0 : s = 0 := by
    have hcomp := congrArg (fun u => u ⬝ᵥ w) hs
    simp only [smul_dotProduct, smul_eq_mul, hunit, mul_one] at hcomp
    rw [hvw] at hcomp
    exact hcomp.symm
  rw [hs0, zero_smul] at hs
  rw [hs] at hvv
  simp only [zero_dotProduct] at hvv
  exact hbz (pow_eq_zero_iff two_ne_zero |>.mp hvv.symm)

/-! ## 4. The unconditional caps of the live pair -/

/-- **THE TRANSVERSE MASS IS STRICTLY POSITIVE** at a `K1` dominator: the
split law prices it as the wedge times the opposite reading, the wedge is at
least one, and the opposite reading is alive. -/
theorem kOne_transverse_pos (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (hbz : D.atom z ⬝ᵥ w ≠ 0) :
    0 < leverageOf (D.atom y) - (D.atom y ⬝ᵥ w) ^ 2 := by
  have hanchor := kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax
  rw [pairAnchor_transverse_split hanchor hunit]
  have hlev := kOne_two_le_leverageSum D hxy hxz hyz hdominates hline hunit hax
  have hbz2 : 0 < (D.atom z ⬝ᵥ w) ^ 2 := by positivity
  nlinarith [hlev, hbz2]

/-- **THE WEIGHT CAP, UNCONDITIONAL ON THE STRATUM.**  At a `K1` dominator
the Parseval cap of the live pair needs no side hypothesis:
`min(t_y, t_z)·(l_y + l_z - 1) <= 1`. -/
theorem kOne_pair_weight_cap_of_null (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (hbz : D.atom z ⬝ᵥ w ≠ 0) :
    min (D.weight y) (D.weight z)
        * (leverageOf (D.atom y) + leverageOf (D.atom z) - 1) ≤ 1 :=
  kOne_pair_weight_cap D hyz
    (kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax) hunit
    (kOne_transverse_pos D hxy hxz hyz hdominates hline hunit hax hbz)

/-- **THE BRACKET WEIGHT CAP.**  The master bracket law meets the Parseval
cap: at a `K1` dominator, `min(t_y, t_z)·[xyz]^2 <= l_x`.  The stratum's own
bracket is priced by its erased leverage at the rate of the smaller live
weight — the weight-carrying currency form of the whole stratum. -/
theorem kOne_bracket_weight_cap (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (hbz : D.atom z ⬝ᵥ w ≠ 0) :
    min (D.weight y) (D.weight z) * atomBracket D x y z ^ 2
      ≤ leverageOf (D.atom x) := by
  have hanchor := kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax
  have hmaster := pairAnchor_bracket_master hanchor hunit hax
  have hcap := kOne_pair_weight_cap_of_null D hxy hxz hyz hdominates hline
    hunit hax hbz
  have hlx : 1 < leverageOf (D.atom x) :=
    kOne_leverage_gt_one D hxy hxz hyz hdominates hline hunit hax
  have hbr : atomBracket D x y z ^ 2
      ≤ (leverageOf (D.atom y) + leverageOf (D.atom z) - 1)
          * leverageOf (D.atom x) := by
    rw [atomBracket, hmaster]
    nlinarith [sq_nonneg (D.atom x ⬝ᵥ D.atom y), sq_nonneg (D.atom x ⬝ᵥ D.atom z)]
  have hmin : 0 ≤ min (D.weight y) (D.weight z) :=
    le_min (D.weight_pos y).le (D.weight_pos z).le
  have hlev := kOne_two_le_leverageSum D hxy hxz hyz hdominates hline hunit hax
  nlinarith [mul_le_mul_of_nonneg_left hbr hmin, hcap, hlx, hlev, hmin]

/-! ## 5. The outside null mass and the forced strict refusal -/

/-- **THE OUTSIDE NULL MASS OF `K1`.**  Parseval read at the null direction:
the outside atoms carry exactly `1 - t_y·beta_y^2 - t_z·beta_z^2` of null
mass.  The erased atom pays nothing, so the whole erased weight is
transferred outside. -/
theorem kOne_outside_null_mass (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {w : Fin 3 → ℝ} (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0) :
    ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.weight d * (D.atom d ⬝ᵥ w) ^ 2
      = 1 - D.weight y * (D.atom y ⬝ᵥ w) ^ 2
          - D.weight z * (D.atom z ⬝ᵥ w) ^ 2 := by
  classical
  have hpar := parseval_probe_form D w
  rw [hunit] at hpar
  have hsplit := Finset.sum_add_sum_compl ({x, y, z} : Finset (Fin 6))
    (fun c => D.weight c * (D.atom c ⬝ᵥ w) ^ 2)
  rw [hpar, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton] at hsplit
  linear_combination hsplit
    - D.weight x * (D.atom x ⬝ᵥ w) * hax

/-- **THE FORCED STRICT REFUSAL.**  A genuine `K1` dominator forces an
outside atom that reads the null direction, and the triple of that atom with
the live pair has STRICTLY NEGATIVE gap determinant — a robustly refused
triple, produced with no tie hypothesis.  The strict wedge floor sets the
rate: `det(S_{yzd} - 1) = -(l_y + l_z - 2)·(q_d.w)^2 < 0`. -/
theorem kOne_exists_strict_refusal (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (hbz : D.atom z ⬝ᵥ w ≠ 0) :
    ∃ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.atom d ⬝ᵥ w ≠ 0 ∧
      (subsetSum D ({y, z, d} : Finset (Fin 6)) - 1).det < 0 := by
  classical
  have hmass := kOne_outside_null_mass D hxy hxz hyz hunit hax
  have h3 := pairAnchor_readings_sq_sum
    (kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax) hunit
  have hpairsum : D.weight y + D.weight z ≤ 1 := by
    have hstep : ∑ c ∈ ({y, z} : Finset (Fin 6)), D.weight c
        ≤ ∑ c, D.weight c :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun c _ _ => (D.weight_pos c).le)
    rw [Finset.sum_insert (by simp [hyz]), Finset.sum_singleton,
      D.weight_sum_one] at hstep
    exact hstep
  have hty : D.weight y < 1 := by linarith [D.weight_pos z, hpairsum]
  have htz : D.weight z < 1 := by linarith [D.weight_pos y, hpairsum]
  have hpos : 0 < ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      D.weight d * (D.atom d ⬝ᵥ w) ^ 2 := by
    rw [hmass]
    nlinarith [h3,
      mul_pos (show (0:ℝ) < 1 - D.weight z by linarith)
        (show (0:ℝ) < (D.atom z ⬝ᵥ w) ^ 2 by positivity),
      mul_nonneg (show (0:ℝ) ≤ 1 - D.weight y by linarith)
        (sq_nonneg (D.atom y ⬝ᵥ w))]
  have hex : ∃ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ), D.atom d ⬝ᵥ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ∑ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        D.weight d * (D.atom d ⬝ᵥ w) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      rw [hcon d hd]
      ring
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨d, hd, hread⟩ := hex
  refine ⟨d, hd, hread, ?_⟩
  have hdy : d ≠ y := by
    intro hcon
    rw [Finset.mem_compl] at hd
    exact hd (by rw [hcon]; simp)
  have hdz : d ≠ z := by
    intro hcon
    rw [Finset.mem_compl] at hd
    exact hd (by rw [hcon]; simp)
  rw [kOne_pairTriple_det D hxy hxz hyz hdominates hline.2.1 hunit hax d hdy hdz]
  have hstrict := kOne_two_lt_leverageSum D hxy hxz hyz hdominates hline hunit
    hax hbz
  have hread2 : 0 < (D.atom d ⬝ᵥ w) ^ 2 := by positivity
  nlinarith [hstrict, hread2]

/-! ## 6. The live pair against the global pair budget -/

/-- **THE LIVE PAIR IS NEVER THE LIGHTEST PAIR OF A `K1` TIE, unless its two
weights are jointly small.**  The sibling's lightest-pair cap prices any
lightest pair by `t_a t_b w_ab <= 1 - t_a - t_b`, while the strict wedge
floor of the stratum forces `w_yz > 1` on the live pair.  If the live pair is
the lightest, the two collide into a pure weight statement:

  `t_y·t_z + t_y + t_z < 1` .

The stratum cannot put its live pair at the bottom of the weight order
without paying for it in the weight simplex — the first cross-arm
consequence of the wedge floor, and a genuine cut in the sixteen-refusal
fight. -/
theorem kOne_lightest_live_pair_weight_bound (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdominates : Dominates D ({x, y, z} : Finset (Fin 6)))
    {w : Fin 3 → ℝ} (hline : GapNullLine D ({x, y, z} : Finset (Fin 6)) w)
    (hunit : w ⬝ᵥ w = 1) (hax : D.atom x ⬝ᵥ w = 0)
    (hbz : D.atom z ⬝ᵥ w ≠ 0)
    (hlight : ∀ c, c ≠ y → c ≠ z →
      D.weight y ≤ D.weight c ∧ D.weight z ≤ D.weight c) :
    D.weight y * D.weight z + D.weight y + D.weight z < 1 := by
  have hcap := isTie_lightest_pair_bracket_mass_cap D htie hyz hlight
  have hwedge : leverageOf (D.atom y) * leverageOf (D.atom z)
      - atomPairing D y z ^ 2
      = leverageOf (D.atom y) + leverageOf (D.atom z) - 1 :=
    pairAnchor_wedge_value
      (kOne_pairAnchor D hxy hxz hyz hdominates hline.2.1 hax) hunit
  rw [hwedge] at hcap
  have hstrict := kOne_two_lt_leverageSum D hxy hxz hyz hdominates hline hunit
    hax hbz
  have hy := D.weight_pos y
  have hz := D.weight_pos z
  nlinarith [hcap, hstrict, hy, hz, mul_pos hy hz]

end Gtz
